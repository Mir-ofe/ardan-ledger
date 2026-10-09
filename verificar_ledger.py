"""Verificador del ledger sellado de pronosticos ARDAN (solo lectura, sin token).

Autocontenido a proposito: este mismo fichero se copia a ardan-ledger para que
cualquiera verifique sin clonar ARDAN. `sellar.py` lo importa por ruta, asi que
la definicion canonica de fila/hash vive UNICAMENTE aqui.

Hora de bloque y corte de las 20:30 (Madrid): la hora del bloque Bitcoin la declara
el minero y su timestamp puede desviarse hasta 2 h de la hora real. Por eso el corte
no se compara de forma exacta, sino con una banda de +-2 h (hora de Madrid del dia
del sorteo):
    bloque <= 18:30            -> valida_prospectiva
    18:30 < bloque <= 22:30    -> pendiente_verificacion (zona dudosa)
    bloque > 22:30             -> no_valido_prospectivo
El sello debe consolidarse con margen antes de las 18:30 para ser valido sin dudas.
(La regla de la fila generada despues de las 20:30 sigue siendo exacta: usa el
ts_utc_generacion declarado, no el bloque.)

Uso:
    python verificar_ledger.py --ledger-dir <clon de ardan-ledger> \
        [--resultados primitiva_resultados.csv] [--historial historial.csv] [--no-red]
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
import urllib.request
from datetime import date, datetime, time, timedelta, timezone
from math import comb
from pathlib import Path
from zoneinfo import ZoneInfo

NOMBRE_LEDGER = "pronosticos_sellados.csv"
DIR_OTS = "ots"
GENESIS_PREV = "0" * 64
TZ_MADRID = ZoneInfo("Europe/Madrid")
HORA_CORTE = time(20, 30)
MARGEN_BLOQUE = timedelta(hours=2)  # desvio maximo del timestamp de bloque

ESTADO_PRONOSTICO = "pronostico"
ESTADO_SIN = "sin_pronostico"
ESTADO_GENESIS = "genesis_historico_no_sellado"
ESTADOS = (ESTADO_PRONOSTICO, ESTADO_SIN, ESTADO_GENESIS)

COLUMNAS = [
    "seq", "fecha_sorteo", "estado", "reemision",
    "N1", "N2", "N3", "N4", "N5", "N6", "R",
    "motor_commit", "motor_src_sha256", "sha256_fuente",
    "ts_utc_generacion", "hash_prev", "hash_fila",
]
_CAMPOS_HASH = COLUMNAS[:-1]  # todo salvo hash_fila (incluye hash_prev)

# Veredictos por fila
V_VALIDA = "valida_prospectiva"
V_PENDIENTE = "pendiente_verificacion"
V_NO_VALIDO = "no_valido_prospectivo"
V_SIN_SELLO = "sin_sello"
V_NO_PUNTUABLE = "no_puntuable"


class LedgerError(Exception):
    pass


# --------------------------------------------------------------------------
# Fila canonica y cadena
# --------------------------------------------------------------------------
def serializar_canonica(fila: dict) -> str:
    partes = []
    for c in _CAMPOS_HASH:
        v = str(fila.get(c, ""))
        if "|" in v or "\n" in v or "\r" in v:
            raise LedgerError(f"campo {c} contiene caracter prohibido (| o salto de linea)")
        partes.append(v)
    return "|".join(partes)


def hash_fila(fila: dict) -> str:
    return hashlib.sha256(serializar_canonica(fila).encode("utf-8")).hexdigest()


def leer_ledger(ruta: Path) -> list[dict]:
    with open(ruta, newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        if r.fieldnames != COLUMNAS:
            raise LedgerError(f"cabecera inesperada: {r.fieldnames}")
        return [dict(x) for x in r]


def escribir_ledger_nuevo(ruta: Path, fila: dict) -> None:
    with open(ruta, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNAS, lineterminator="\n")
        w.writeheader()
        w.writerow({c: fila.get(c, "") for c in COLUMNAS})


def anexar_fila(ruta: Path, fila: dict) -> None:
    with open(ruta, "a", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNAS, lineterminator="\n")
        w.writerow({c: fila.get(c, "") for c in COLUMNAS})


def verificar_cadena(filas: list[dict]) -> list[str]:
    """Errores de integridad. Lista vacia = cadena integra."""
    errores = []
    prev = GENESIS_PREV
    for i, f in enumerate(filas):
        if f.get("seq") != str(i):
            errores.append(f"fila {i}: seq={f.get('seq')!r} (esperado {i}) -- fila eliminada, insertada o reordenada")
        if f.get("estado") not in ESTADOS:
            errores.append(f"fila {i}: estado desconocido {f.get('estado')!r}")
        if f.get("hash_prev") != prev:
            errores.append(f"fila {i}: hash_prev no encadena con la fila anterior")
        try:
            esperado = hash_fila(f)
        except LedgerError as e:
            errores.append(f"fila {i}: {e}")
            esperado = None
        if esperado is not None and f.get("hash_fila") != esperado:
            errores.append(f"fila {i}: hash_fila no coincide (contenido alterado)")
        prev = f.get("hash_fila", "")
    if filas and filas[0].get("estado") != ESTADO_GENESIS:
        errores.append("la fila 0 no es el genesis")
    return errores


# --------------------------------------------------------------------------
# OpenTimestamps
# --------------------------------------------------------------------------
def rutas_sello(dir_ledger: Path, seq: int) -> tuple[Path, Path]:
    base = dir_ledger / DIR_OTS / f"{int(seq):06d}.head"
    return base, base.with_name(base.name + ".ots")


EXPLORADORES = ("https://mempool.space/api", "https://blockstream.info/api")  # misma API (esplora)
_RE_BLOQUE = re.compile(r"BitcoinBlockHeaderAttestation\((\d+)\)")


class ExploradorBloques:
    """Hora (UTC) de un bloque de Bitcoin por altura. Primero mempool.space, respaldo blockstream.info.
    Devuelve None si ninguno responde: el veredicto queda pendiente_verificacion, nunca se adivina."""

    def __init__(self, bases=EXPLORADORES, fetch=None):
        self.bases = bases
        self.fetch = fetch or self._fetch_http

    @staticmethod
    def _fetch_http(url: str) -> str:
        with urllib.request.urlopen(url, timeout=30) as r:
            return r.read().decode("utf-8")

    def hora_bloque(self, altura: int) -> "datetime | None":
        for base in self.bases:
            try:
                h = self.fetch(f"{base}/block-height/{int(altura)}").strip()
                if not re.fullmatch(r"[0-9a-f]{64}", h):
                    continue
                ts = json.loads(self.fetch(f"{base}/block/{h}"))["timestamp"]
                return datetime.fromtimestamp(int(ts), tz=timezone.utc)
            except Exception:
                continue
        return None


class ClienteOTS:
    """Envoltorio del CLI `ots`. Los tests lo sustituyen por un doble."""

    def __init__(self, binario: str = "ots", runner=subprocess.run, explorador: "ExploradorBloques | None" = None):
        self.binario = binario
        self.runner = runner
        self.explorador = explorador or ExploradorBloques()

    def _run(self, *args):
        return self.runner([self.binario, *args], capture_output=True, text=True, timeout=300)

    def stamp(self, fichero: Path) -> None:
        r = self._run("stamp", str(fichero))
        if r.returncode != 0:
            raise LedgerError(f"ots stamp fallo (rc={r.returncode}): {(r.stderr or r.stdout)[-300:]}")

    def upgrade(self, ots: Path) -> None:
        self._run("upgrade", str(ots))  # rc != 0 si sigue pendiente; no es error

    def verificar(self, ots: Path) -> tuple[str, "datetime | None"]:
        """('pendiente'|'completo'|'invalido', hora UTC del bloque de Bitcoin o None).

        `ots info` da la altura del bloque atestiguado; la hora sale del explorador de bloques.
        Sin atestacion Bitcoin o sin explorador disponible -> 'pendiente' (no se infiere nada).
        """
        r = self._run("info", str(ots))
        if r.returncode != 0:
            return "invalido", None
        alturas = [int(a) for a in _RE_BLOQUE.findall((r.stdout or "") + (r.stderr or ""))]
        if not alturas:
            return "pendiente", None
        hora = self.explorador.hora_bloque(min(alturas))
        if hora is None:
            return "pendiente", None
        return "completo", hora


def limite_prospectivo(fecha_sorteo: str) -> datetime:
    """20:30 Europe/Madrid del dia del sorteo, en UTC."""
    d = date.fromisoformat(fecha_sorteo)
    return datetime.combine(d, HORA_CORTE, tzinfo=TZ_MADRID).astimezone(timezone.utc)


def _parse_ts(ts: str) -> datetime:
    return datetime.fromisoformat(ts.replace("Z", "+00:00")).astimezone(timezone.utc)


def veredicto_fila(fila: dict, dir_ledger: Path, cliente: "ClienteOTS | None") -> tuple[str, str]:
    """(veredicto, motivo) para una fila. Solo reemision==0 con estado pronostico puede ser prospectiva."""
    if fila["estado"] != ESTADO_PRONOSTICO:
        return V_NO_PUNTUABLE, f"estado={fila['estado']}"
    if fila["reemision"] != "0":
        return V_NO_PUNTUABLE, f"reemision={fila['reemision']} (solo la primera emision cuenta)"
    limite = limite_prospectivo(fila["fecha_sorteo"])
    if _parse_ts(fila["ts_utc_generacion"]) > limite:
        return V_NO_VALIDO, "generada despues del corte (20:30 Madrid del dia del sorteo)"
    head, ots = rutas_sello(dir_ledger, int(fila["seq"]))
    if not head.exists() or not ots.exists():
        return V_SIN_SELLO, "falta el fichero .head o .ots de esta fila"
    if head.read_text(encoding="utf-8").strip() != fila["hash_fila"]:
        return V_NO_VALIDO, "el sello no corresponde al hash_fila"
    if cliente is None:
        return V_PENDIENTE, "verificacion OTS omitida (--no-red)"
    cliente.upgrade(ots)
    estado, ts = cliente.verificar(ots)
    if estado == "invalido":
        return V_NO_VALIDO, "sello OTS invalido"
    if estado == "pendiente":
        return V_PENDIENTE, "sin atestacion Bitcoin verificable aun (sello pendiente o explorador no disponible)"
    ts = ts.astimezone(timezone.utc)
    if ts <= limite - MARGEN_BLOQUE:
        return V_VALIDA, f"sello Bitcoin (bloque {ts:%Y-%m-%d %H:%M}Z) anterior a la banda del corte (<=18:30 Madrid)"
    if ts <= limite + MARGEN_BLOQUE:
        return V_PENDIENTE, f"sello Bitcoin (bloque {ts:%Y-%m-%d %H:%M}Z) dentro de la banda +-2 h del corte (18:30-22:30 Madrid)"
    return V_NO_VALIDO, f"sello Bitcoin (bloque {ts:%Y-%m-%d %H:%M}Z) posterior a la banda del corte (>22:30 Madrid)"


def verificar_ots_huerfanos(filas: list[dict], dir_ledger: Path) -> list[str]:
    """Un sello cuyo seq/hash no esta en la cadena delata truncado o reescritura."""
    errores = []
    d = dir_ledger / DIR_OTS
    if not d.exists():
        return errores
    por_seq = {f["seq"]: f for f in filas}
    for head in sorted(d.glob("*.head")):
        seq = str(int(head.stem))
        f = por_seq.get(seq)
        if f is None:
            errores.append(f"{head.name}: sello de una fila que ya no esta en el ledger (truncado?)")
        elif head.read_text(encoding="utf-8").strip() != f["hash_fila"]:
            errores.append(f"{head.name}: el hash sellado no coincide con la fila {seq} (reescritura)")
    return errores


# --------------------------------------------------------------------------
# Drive vs ledger
# --------------------------------------------------------------------------
def _nums_drive(row: dict) -> "tuple | None":
    try:
        return tuple(sorted(int(float(row[f"N{i}_pred"])) for i in range(1, 7)))
    except (KeyError, ValueError, TypeError):
        return None


def comparar_historial(filas: list[dict], ruta_historial: Path) -> list[str]:
    """Avisos de discrepancia entre la copia de trabajo (Drive) y el ledger."""
    avisos = []
    genesis = next((f for f in filas if f["estado"] == ESTADO_GENESIS), None)
    corte = _parse_ts(genesis["ts_utc_generacion"]).date() if genesis else None
    primeras = {f["fecha_sorteo"]: f for f in filas
                if f["estado"] == ESTADO_PRONOSTICO and f["reemision"] == "0"}
    with open(ruta_historial, newline="", encoding="utf-8-sig") as fh:
        drive = list(csv.DictReader(fh, delimiter=";"))
    vistas = set()
    for row in drive:
        fecha = (row.get("fecha_sorteo_aplica") or "").strip()
        nums = _nums_drive(row)
        if not fecha or nums is None:
            continue
        vistas.add(fecha)
        f = primeras.get(fecha)
        if f is None:
            if corte and date.fromisoformat(fecha) > corte:
                avisos.append(f"{fecha}: en Drive pero NO sellado en el ledger")
            continue
        n_ledger = tuple(sorted(int(f[f"N{i}"]) for i in range(1, 7)))
        if n_ledger != nums:
            avisos.append(f"{fecha}: Drive {nums} != ledger {n_ledger}")
    for fecha in primeras:
        if fecha not in vistas:
            avisos.append(f"{fecha}: sellado en el ledger pero ausente en Drive")
    return avisos


# --------------------------------------------------------------------------
# Puntuacion contra azar
# --------------------------------------------------------------------------
def _pmf_hits(k: int) -> float:
    return comb(6, k) * comb(43, 6 - k) / comb(49, 6)


def _cola_suma(n: int, total: int) -> float:
    """P(suma de n aciertos hipergeometricos >= total) bajo azar puro, exacto."""
    dist = {0: 1.0}
    for _ in range(n):
        nueva: dict[int, float] = {}
        for s, p in dist.items():
            for k in range(7):
                nueva[s + k] = nueva.get(s + k, 0.0) + p * _pmf_hits(k)
        dist = nueva
    return sum(p for s, p in dist.items() if s >= total)


def cargar_resultados(ruta: Path) -> dict[str, set]:
    with open(ruta, newline="", encoding="utf-8-sig") as fh:
        muestra = fh.read(2048)
        fh.seek(0)
        delim = ";" if muestra.count(";") > muestra.count(",") else ","
        out = {}
        for r in csv.DictReader(fh, delimiter=delim):
            try:
                out[r["Fecha"].strip()] = {int(float(r[f"N{i}"])) for i in range(1, 7)}
            except (KeyError, ValueError):
                continue
    return out


def puntuar(filas_validas: list[dict], resultados: dict[str, set]) -> dict:
    hits = []
    for f in filas_validas:
        real = resultados.get(f["fecha_sorteo"])
        if real is None:
            continue
        hits.append(len({int(f[f"N{i}"]) for i in range(1, 7)} & real))
    n = len(hits)
    esperado = 36 / 49
    return {
        "n_puntuadas": n,
        "n_validas_sin_resultado": len(filas_validas) - n,
        "aciertos_medios": (sum(hits) / n) if n else None,
        "aciertos_esperados_azar": esperado,
        "n_3_o_mas": sum(1 for h in hits if h >= 3),
        "p_3_o_mas_azar": sum(_pmf_hits(k) for k in range(3, 7)),
        "p_valor_suma_aciertos": _cola_suma(n, sum(hits)) if n else None,
    }


# --------------------------------------------------------------------------
# Orquestacion
# --------------------------------------------------------------------------
def verificar(dir_ledger: Path, resultados: "Path | None" = None, historial: "Path | None" = None,
              cliente: "ClienteOTS | None" = None) -> dict:
    ruta = Path(dir_ledger) / NOMBRE_LEDGER
    filas = leer_ledger(ruta)
    errores = verificar_cadena(filas) + verificar_ots_huerfanos(filas, Path(dir_ledger))
    veredictos = {}
    if not errores:
        for f in filas:
            veredictos[int(f["seq"])] = veredicto_fila(f, Path(dir_ledger), cliente)
    validas = [f for f in filas if veredictos.get(int(f["seq"]), ("",))[0] == V_VALIDA]
    informe = {
        "integra": not errores,
        "errores": errores,
        "n_filas": len(filas),
        "veredictos": veredictos,
        "avisos_drive": comparar_historial(filas, Path(historial)) if historial and not errores else [],
        "puntuacion": None,
    }
    if resultados and not errores:
        informe["puntuacion"] = puntuar(validas, cargar_resultados(Path(resultados)))
    return informe


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger-dir", required=True)
    ap.add_argument("--resultados")
    ap.add_argument("--historial")
    ap.add_argument("--no-red", action="store_true", help="no consultar OpenTimestamps")
    a = ap.parse_args(argv)
    inf = verificar(Path(a.ledger_dir), a.resultados, a.historial,
                    None if a.no_red else ClienteOTS())
    print(f"filas: {inf['n_filas']} | cadena integra: {inf['integra']}")
    for e in inf["errores"]:
        print("ERROR:", e)
    for seq, (v, m) in inf["veredictos"].items():
        if v != V_NO_PUNTUABLE:
            print(f"  seq {seq}: {v} -- {m}")
    for av in inf["avisos_drive"]:
        print("AVISO Drive/ledger:", av)
    if inf["puntuacion"]:
        print("PUNTUACION (solo reemision==0 validas):", inf["puntuacion"])
    return 0 if inf["integra"] else 1


if __name__ == "__main__":
    sys.exit(main())
