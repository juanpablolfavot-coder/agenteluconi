"""
AGENTE IA - Monitor de Flota RutaSat v1.6

Plataforma GPS: RutaSat (https://rutasat.com/api/)
Notificaciones: WhatsApp via Twilio
Alertas: Exceso de velocidad, Ralenti, Reporte horario, Resumen diario
Extras: Clima (Open-Meteo, gratis) + Trafico (TomTom, opcional)
Cierre 18hs: inicio de jornada, fin de jornada, viajes y paradas por patente

Cambios v1.6:
- Límite general de ruta: 80 km/h
- Límite 110 km/h SOLO para patentes cargadas en PATENTES_110
- Antes de 20:30: reporte horario SOLO si hay vehículos en movimiento
- El reporte horario muestra SOLO los vehículos en movimiento
- Ubicación en reporte como coordenadas, SIN links de Maps
- Después de 20:30: NO hay reporte horario; solo alerta automática si algún vehículo se mueve
- Ralenti excluido SOLO para Motomel gris A241VOY (46)
- Fix cierre 18hs: extrae patente real desde el nombre del dispositivo en RutaSat
- Mensajes largos de WhatsApp se parten en varios bloques para evitar error 21617
- Soporte para ADMIN4_WHATSAPP
"""

from utils_env import load_env
load_env(".envvars")

import time
import csv
import os
import json
import re
import traceback
import requests
from datetime import datetime, timezone, timedelta

from twilio.rest import Client
import anthropic


# ---------------------------------------------------------------------------
# CONFIG
# ---------------------------------------------------------------------------
RUTASAT_BASE_URL  = "https://rutasat.com/api"
RUTASAT_EMAIL     = os.getenv("RUTASAT_EMAIL", "")
RUTASAT_PASSWORD  = os.getenv("RUTASAT_PASSWORD", "")

TWILIO_ACCOUNT_SID   = os.getenv("TWILIO_ACCOUNT_SID", "")
TWILIO_AUTH_TOKEN    = os.getenv("TWILIO_AUTH_TOKEN", "")
TWILIO_WHATSAPP_FROM = os.getenv("TWILIO_WHATSAPP_FROM", "")
TWILIO_CONTENT_SID   = os.getenv("TWILIO_CONTENT_SID", "")

ADMIN_WHATSAPP  = os.getenv("ADMIN_WHATSAPP", "")
ADMIN2_WHATSAPP = os.getenv("ADMIN2_WHATSAPP", "")
ADMIN3_WHATSAPP = os.getenv("ADMIN3_WHATSAPP", "")
ADMIN4_WHATSAPP = os.getenv("ADMIN4_WHATSAPP", "")

ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")
TOMTOM_API_KEY    = os.getenv("TOMTOM_API_KEY", "")

POLL_SECONDS       = int(os.getenv("POLL_SECONDS", "120"))
LIMITE_RUTA        = int(os.getenv("LIMITE_RUTA", "80"))
LIMITE_URBANO      = int(os.getenv("LIMITE_URBANO", "60"))
IDLE_MINUTES       = int(os.getenv("IDLE_MINUTES", "5"))
MOVEMENT_MIN_SPEED = int(os.getenv("MOVEMENT_MIN_SPEED", "5"))

# Ventana fuera de horario
AFTER_HOURS_START = os.getenv("AFTER_HOURS_START", "20:30")
AFTER_HOURS_END   = os.getenv("AFTER_HOURS_END", "05:00")

# Margen seguro para Twilio WhatsApp
MAX_WA_BODY = int(os.getenv("MAX_WA_BODY", "1300"))

SPEED_EXCEED_MINUTES = 3

# Zonas urbanas — ajustar segun la empresa
URBAN_BBOXES = {
    "RIO_TERCERO": (-32.20, -64.14, -32.12, -64.05),
    "CORDOBA":     (-31.47, -64.26, -31.33, -64.10),
    "CABA":        (-34.71, -58.53, -34.53, -58.33),
}

# Nombres de dispositivos a ignorar (mayusculas normalizadas)
DISPOSITIVOS_EXCLUIDOS: set = set()

# Excluir ralenti solo para esta unidad
RALENTI_EXCLUIDOS_MATCH: set = {
    "A241VOY",
}


# ---------------------------------------------------------------------------
# UTILS DE PATENTES
# ---------------------------------------------------------------------------
def normalize_plate(text):
    return re.sub(r"[^A-Z0-9]", "", (text or "").upper())


def extract_plate_from_name(text):
    """
    Extrae patente real desde nombres como:
    - Moto A073EQT ALE BRIGNONE (52)
    - Kangoo/ORF342 (04)
    - Iveco 56 AF195QL
    - Sandero AG677LX(33)
    """
    raw = (text or "").upper()

    patterns = [
        r"\b([A-Z]{2}\d{3}[A-Z]{2})\b",  # AF195QL / AA706VW
        r"\b([A-Z]\d{3}[A-Z]{3})\b",     # A073EQT / A241VOY
        r"\b([A-Z]{3}\d{3})\b",          # ORF347 / JFV680
    ]

    for pat in patterns:
        m = re.search(pat, raw)
        if m:
            return m.group(1)

    compact = re.sub(r"[^A-Z0-9]", "", raw)

    for pat in [
        r"([A-Z]{2}\d{3}[A-Z]{2})",
        r"([A-Z]\d{3}[A-Z]{3})",
        r"([A-Z]{3}\d{3})",
    ]:
        m = re.search(pat, compact)
        if m:
            return m.group(1)

    return ""


# ---------------------------------------------------------------------------
# VEHÍCULOS CON LÍMITE 110 km/h (autopista / ruta nacional)
# SOLO por patente, en MAYÚSCULAS y sin espacios ni guiones
# ---------------------------------------------------------------------------
PATENTES_110: set = {
    # Kangoo
    "ORF347", "ORF342",
    # KWID
    "AH156HY", "AH56HX",
    # Sandero
    "AG369ZD", "AG369ZC", "AG677LX", "AG677LW",
}

# ---------------------------------------------------------------------------
# MAPA PATENTE → NOMBRE LEGIBLE
# ---------------------------------------------------------------------------
NOMBRE_VEHICULO = {
    "ORF347":  "Kangoo EX.1.6 #1",
    "ORF342":  "Kangoo EX.1.6 #2",
    "KCB412":  "Partner 1.6 HDI",
    "AH156HY": "KWID #1",
    "AH56HX":  "KWID #2",
    "AG369ZD": "Sandero #1",
    "AG369ZC": "Sandero #2",
    "AG677LX": "Sandero #3",
    "AG677LW": "Sandero #4",
    "JFV680":  "VW Fox 1.6",
}

# ---------------------------------------------------------------------------
# PATENTES PARA REPORTE DE CIERRE 18HS
# ---------------------------------------------------------------------------
PATENTES_REPORTE_18: set = {
    "AH156HY",
    "AH56HX",
    "ORF347",
    "A073EQT",
    "AG369ZD",
    "AG369ZC",
    "A161TWU",
    "ORF342",
    "A255DSL",
    "AG677LX",
    "AG677LW",
    "JFV680",
    "A198FWP",
    "A255DSK",
    "A255DSJ",
    "A276PHM",
    "A276PHN",
    "A198FWR",
}


def get_speed_limit(vehicle):
    """Devuelve el límite de velocidad para un vehículo dado."""
    lat   = vehicle["lat"]
    lng   = vehicle["lng"]
    plate = normalize_plate(vehicle["plate"])

    if is_in_urban(lat, lng):
        return LIMITE_URBANO, "URBANO"

    if plate in PATENTES_110:
        return 110, "RUTA-110"

    return LIMITE_RUTA, "RUTA"


def display_name(plate, raw_name=None):
    """
    Si la patente está mapeada devuelve 'PATENTE (Modelo)'.
    Si no, usa el nombre real del equipo si existe.
    """
    clean  = normalize_plate(plate)
    nombre = NOMBRE_VEHICULO.get(clean)
    if nombre:
        return f"{clean} ({nombre})"
    if raw_name:
        return str(raw_name).strip()
    return clean


def get_admin_numbers():
    return [x for x in [ADMIN_WHATSAPP, ADMIN2_WHATSAPP, ADMIN3_WHATSAPP, ADMIN4_WHATSAPP] if x]


# ---------------------------------------------------------------------------
# ESTADO GLOBAL
# ---------------------------------------------------------------------------
alert_history         = {}
daily_events          = []
last_hourly_report    = 0   # 0 = envia al arrancar

idle_tracking             = {}
idle_alerted              = {}
speed_exceed_tracking     = {}
after_hours_motion_state  = {}

weather_cache         = {}
traffic_cache         = {}
wa_session_active     = {}

_rutasat_token        = None
_rutasat_token_expiry = 0


# ---------------------------------------------------------------------------
# UTILS
# ---------------------------------------------------------------------------
def now_iso():
    return datetime.now(timezone.utc).isoformat()

def now_local():
    return datetime.now(timezone(timedelta(hours=-3)))

def is_in_urban(lat, lng):
    for _, (min_lat, min_lng, max_lat, max_lng) in URBAN_BBOXES.items():
        if min_lat <= lat <= max_lat and min_lng <= lng <= max_lng:
            return True
    return False

def maps_link(lat, lng):
    return f"https://maps.google.com/?q={lat},{lng}"

def format_coords(lat, lng):
    return f"{float(lat):.5f}, {float(lng):.5f}"


def knots_to_kmh(knots):
    """RutaSat devuelve velocidad en nudos."""
    return float(knots or 0) * 1.852

def iso_utc(dt):
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

def parse_dt_local(value):
    if not value:
        return None
    try:
        return datetime.fromisoformat(str(value).replace("Z", "+00:00")).astimezone(
            timezone(timedelta(hours=-3))
        )
    except Exception:
        return None

def hhmm(value):
    dt = parse_dt_local(value)
    return dt.strftime("%H:%M") if dt else "--:--"

def parse_hhmm(text, default=(20, 30)):
    try:
        h, m = str(text).strip().split(":")
        h = int(h)
        m = int(m)
        if 0 <= h <= 23 and 0 <= m <= 59:
            return h, m
    except Exception:
        pass
    return default

AFTER_HOURS_START_HM = parse_hhmm(AFTER_HOURS_START, (20, 30))
AFTER_HOURS_END_HM   = parse_hhmm(AFTER_HOURS_END,   (5, 0))

def is_after_hours(dt=None):
    """
    Ventana fuera de horario.
    Por defecto: desde 20:30 hasta 05:00 del día siguiente.
    """
    dt = dt or now_local()
    hm = (dt.hour, dt.minute)

    start = AFTER_HOURS_START_HM
    end   = AFTER_HOURS_END_HM

    if start <= end:
        return start <= hm < end

    return hm >= start or hm < end


def is_idle_excluded(vehicle):
    """
    Excluye de alerta de ralenti SOLO a la unidad Motomel gris A241VOY (46).
    Busca por coincidencia para tolerar distintos formatos de nombre.
    """
    plate_txt = normalize_plate(vehicle.get("plate", ""))
    name_txt  = normalize_plate(vehicle.get("name", ""))

    for token in RALENTI_EXCLUIDOS_MATCH:
        token_norm = normalize_plate(token)
        if token_norm and (token_norm in plate_txt or token_norm in name_txt):
            return True
    return False


def split_whatsapp_text(text, limit=MAX_WA_BODY):
    """
    Parte un mensaje largo en bloques seguros para Twilio.
    Prioriza cortes por salto de linea o espacio.
    """
    text = (text or "").strip()
    if not text:
        return []

    hard_limit = max(200, limit - 12)

    parts = []
    current = ""

    for raw_line in text.splitlines():
        line = raw_line.rstrip()

        if not current:
            candidate = line
        else:
            candidate = current + "\n" + line

        if len(candidate) <= hard_limit:
            current = candidate
            continue

        if current:
            parts.append(current)
            current = ""

        while len(line) > hard_limit:
            cut = line.rfind(" ", 0, hard_limit)
            if cut < hard_limit // 2:
                cut = hard_limit
            parts.append(line[:cut].rstrip())
            line = line[cut:].lstrip()

        current = line

    if current:
        parts.append(current)

    if len(parts) <= 1:
        return parts

    total = len(parts)
    return [f"({i}/{total})\n{part}" for i, part in enumerate(parts, 1)]


# ---------------------------------------------------------------------------
# RUTASAT API
# ---------------------------------------------------------------------------
def get_rutasat_token():
    global _rutasat_token, _rutasat_token_expiry
    ahora = time.time()
    if _rutasat_token and ahora < _rutasat_token_expiry:
        return _rutasat_token

    session = requests.Session()

    r1 = session.post(
        f"{RUTASAT_BASE_URL}/session",
        data={"email": RUTASAT_EMAIL, "password": RUTASAT_PASSWORD},
        timeout=15,
    )
    r1.raise_for_status()

    expiration = (datetime.now(timezone.utc) + timedelta(days=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    r2 = session.post(
        f"{RUTASAT_BASE_URL}/session/token",
        data={"expiration": expiration},
        timeout=15,
    )
    r2.raise_for_status()

    _rutasat_token        = r2.text.strip()
    _rutasat_token_expiry = ahora + (29 * 86400)
    print("  RutaSat token OK (expira en 30 dias)")
    return _rutasat_token


def rutasat_get(path, params=None):
    token = get_rutasat_token()
    headers = {"Authorization": f"Bearer {token}", "Accept": "application/json"}
    r = requests.get(f"{RUTASAT_BASE_URL}{path}", headers=headers, params=params, timeout=20)
    r.raise_for_status()
    return r.json()


def get_devices():
    return rutasat_get("/devices")

def get_positions():
    return rutasat_get("/positions")


def _extract_report_rows(data):
    """
    Normaliza distintas respuestas posibles de RutaSat:
    - lista directa
    - dict con 'data'
    - dict con 'items'
    - dict con 'result'
    """
    if isinstance(data, list):
        return data
    if isinstance(data, dict):
        for key in ("data", "items", "result"):
            if isinstance(data.get(key), list):
                return data[key]
    return []


def get_report_trips(device_id, from_dt, to_dt):
    """
    Historial de viajes del vehículo dentro del rango.
    Si tu cuenta usa otro endpoint, ajustá SOLO esta función.
    """
    try:
        data = rutasat_get(
            "/reports/trips",
            params={
                "deviceId": device_id,
                "from": iso_utc(from_dt),
                "to": iso_utc(to_dt),
            },
        )
        return _extract_report_rows(data)
    except Exception as e:
        print(f"  Error reports/trips device {device_id}: {e}")
        return []


def get_report_stops(device_id, from_dt, to_dt):
    """
    Historial de paradas del vehículo dentro del rango.
    Si tu cuenta usa otro endpoint, ajustá SOLO esta función.
    """
    try:
        data = rutasat_get(
            "/reports/stops",
            params={
                "deviceId": device_id,
                "from": iso_utc(from_dt),
                "to": iso_utc(to_dt),
            },
        )
        return _extract_report_rows(data)
    except Exception as e:
        print(f"  Error reports/stops device {device_id}: {e}")
        return []


def build_vehicle_list(devices, positions):
    device_map = {d["id"]: d for d in devices}
    vehicles   = []

    for pos in positions:
        device_id = pos.get("deviceId")
        device    = device_map.get(device_id, {})
        name      = (device.get("name", str(device_id)) or "").strip()

        plate = extract_plate_from_name(name)
        if not plate:
            plate = normalize_plate(name) or str(device_id)

        if plate in DISPOSITIVOS_EXCLUIDOS:
            continue

        attrs    = pos.get("attributes", {})
        ignition = bool(attrs.get("ignition", False))

        vehicles.append({
            "plate":       plate,
            "device_id":   device_id,
            "name":        name,
            "lat":         float(pos.get("latitude",  0) or 0),
            "lng":         float(pos.get("longitude", 0) or 0),
            "speed_kmh":   knots_to_kmh(pos.get("speed", 0)),
            "ignition":    ignition,
            "last_update": pos.get("deviceTime", ""),
        })
    return vehicles


def build_devices_lookup_by_plate(devices):
    out = {}
    for d in devices:
        name = (d.get("name") or "").strip()
        plate = extract_plate_from_name(name)
        if plate:
            out[plate] = d
    return out


# ---------------------------------------------------------------------------
# WHATSAPP (Twilio)
# ---------------------------------------------------------------------------
def _send_single_whatsapp(client, to, body, has_session):
    """
    Envia un solo bloque de mensaje.
    Si hay ventana activa de 24h intenta body directo.
    Si no, intenta template si existe.
    """
    if has_session:
        try:
            return client.messages.create(
                from_=TWILIO_WHATSAPP_FROM,
                to=to,
                body=body,
            )
        except Exception as e:
            if "63112" in str(e):
                wa_session_active.pop(to, None)
                has_session = False
            else:
                raise

    if TWILIO_CONTENT_SID:
        try:
            msg = client.messages.create(
                from_=TWILIO_WHATSAPP_FROM,
                to=to,
                content_sid=TWILIO_CONTENT_SID,
                content_variables=json.dumps({"1": body}),
            )
            print(f"  Enviado con template a {to}")
            return msg
        except Exception as e:
            print(f"  Error template: {e}")

    return client.messages.create(
        from_=TWILIO_WHATSAPP_FROM,
        to=to,
        body=body,
    )


def send_whatsapp(client, to, body):
    body = (body or "").strip()
    if not body:
        return []

    ahora       = time.time()
    has_session = (ahora - wa_session_active.get(to, 0)) < 86400

    partes = split_whatsapp_text(body, MAX_WA_BODY)
    enviados = []

    for parte in partes:
        try:
            enviados.append(_send_single_whatsapp(client, to, parte, has_session))
        except Exception as e:
            if "21617" in str(e) and len(parte) > 500:
                subpartes = split_whatsapp_text(parte, 800)
                for sub in subpartes:
                    enviados.append(_send_single_whatsapp(client, to, sub, has_session))
            else:
                raise

    return enviados


def send_to_admins(client, body):
    for admin in get_admin_numbers():
        try:
            send_whatsapp(client, admin, body)
        except Exception as e:
            print(f"  Error enviando a {admin}: {e}")


# ---------------------------------------------------------------------------
# LOG CSV
# ---------------------------------------------------------------------------
def log_event(row, path="logs_alertas_rutasat.csv"):
    exists = os.path.exists(path)
    with open(path, "a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(row.keys()))
        if not exists:
            writer.writeheader()
        writer.writerow(row)


# ---------------------------------------------------------------------------
# CLIMA (Open-Meteo — gratis, sin API key)
# ---------------------------------------------------------------------------
def get_weather(lat, lng):
    cache_key = f"{lat:.2f},{lng:.2f}"
    ahora     = time.time()
    if cache_key in weather_cache and (ahora - weather_cache[cache_key]["ts"]) < 3600:
        return weather_cache[cache_key]["data"]
    try:
        url = (
            "https://api.open-meteo.com/v1/forecast"
            f"?latitude={lat}&longitude={lng}"
            "&current=temperature_2m,apparent_temperature,precipitation,"
            "rain,weather_code,wind_speed_10m,wind_gusts_10m"
            "&timezone=America/Argentina/Cordoba"
        )
        r = requests.get(url, timeout=10)
        r.raise_for_status()
        data = r.json().get("current", {})
        info = {
            "temp":          data.get("temperature_2m"),
            "feels_like":    data.get("apparent_temperature"),
            "precipitation": data.get("precipitation", 0),
            "rain":          data.get("rain", 0),
            "wind_speed":    data.get("wind_speed_10m"),
            "wind_gusts":    data.get("wind_gusts_10m"),
            "weather_code":  data.get("weather_code", 0),
            "description":   _wcode(data.get("weather_code", 0)),
        }
        weather_cache[cache_key] = {"ts": ahora, "data": info}
        return info
    except Exception as e:
        print(f"  Error clima: {e}")
        return None


def _wcode(code):
    codes = {
        0:"Despejado", 1:"Mayormente despejado", 2:"Parcialmente nublado", 3:"Nublado",
        45:"Niebla", 48:"Niebla con escarcha",
        51:"Llovizna leve", 53:"Llovizna moderada", 55:"Llovizna intensa",
        61:"Lluvia leve", 63:"Lluvia moderada", 65:"Lluvia intensa",
        71:"Nevada leve", 73:"Nevada moderada", 75:"Nevada intensa",
        80:"Chubascos leves", 81:"Chubascos moderados", 82:"Chubascos violentos",
        95:"Tormenta electrica", 99:"Tormenta con granizo",
    }
    return codes.get(code, f"Codigo {code}")


def format_weather_short(w):
    if not w:
        return "sin datos"
    msg   = f"{w.get('description','?')}, {w.get('temp','?')}C (ST {w.get('feels_like','?')}C)"
    wind  = w.get("wind_speed", 0) or 0
    gusts = w.get("wind_gusts", 0) or 0
    rain  = w.get("rain", 0) or 0
    if wind  > 20:
        msg += f", viento {wind:.0f}km/h"
    if gusts > 40:
        msg += f" (rafagas {gusts:.0f})"
    if rain  > 0:
        msg += f", lluvia {rain:.1f}mm"
    return msg


def is_weather_risky(w):
    if not w:
        return False, ""
    risks = []
    code  = w.get("weather_code", 0)
    gusts = w.get("wind_gusts", 0) or 0
    rain  = w.get("rain", 0) or 0
    if code >= 61:
        risks.append("lluvia/tormenta")
    elif code >= 51:
        risks.append("llovizna")
    if code in (45, 48):
        risks.append("niebla")
    if gusts > 60:
        risks.append(f"rafagas {gusts:.0f}km/h")
    if rain > 5:
        risks.append(f"lluvia {rain:.1f}mm")
    return bool(risks), ", ".join(risks)


# ---------------------------------------------------------------------------
# TRAFICO (TomTom — opcional)
# ---------------------------------------------------------------------------
def get_traffic_incidents(lat, lng, radius_km=5):
    if not TOMTOM_API_KEY:
        return None

    cache_key = f"{lat:.2f},{lng:.2f}"
    ahora     = time.time()
    if cache_key in traffic_cache and (ahora - traffic_cache[cache_key]["ts"]) < 600:
        return traffic_cache[cache_key]["data"]

    try:
        delta = radius_km / 111.0
        bbox  = f"{lng-delta:.4f},{lat-delta:.4f},{lng+delta:.4f},{lat+delta:.4f}"
        url   = "https://api.tomtom.com/traffic/services/5/incidentDetails"
        params = {
            "key":      TOMTOM_API_KEY,
            "bbox":     bbox,
            "fields":   "{incidents{type,geometry{type,coordinates},properties{iconCategory,magnitudeOfDelay,events{description,code},from,to,length,delay,roadNumbers}}}",
            "language": "es-ES",
        }
        r = requests.get(url, params=params, timeout=10)
        if r.status_code == 400:
            params.pop("fields", None)
            r = requests.get(url, params=params, timeout=10)
        r.raise_for_status()
        data = r.json()

        incidents = []
        for inc in data.get("incidents", []):
            props = inc.get("properties", {})
            icon  = props.get("iconCategory", 0)
            incidents.append({
                "category":  _tomtom_cat(icon),
                "icon":      icon,
                "from":      props.get("from", ""),
                "delay":     props.get("delay") or 0,
                "magnitude": props.get("magnitudeOfDelay", 0),
                "events":    [e.get("description", "") for e in props.get("events", []) if e.get("description")],
            })

        traffic_cache[cache_key] = {"ts": ahora, "data": incidents}
        return incidents
    except Exception as e:
        print(f"  Error trafico: {e}")
        return None


def _tomtom_cat(icon):
    cats = {
        0:"Desconocido", 1:"Accidente", 2:"Niebla", 3:"Peligro",
        4:"Lluvia", 5:"Hielo", 6:"Congestion", 7:"Viento",
        8:"Corte de calle", 9:"Obras", 10:"Cierre de carril",
        11:"Corte de ruta", 14:"Ruta bloqueada",
    }
    return cats.get(icon, f"Tipo {icon}")


def format_traffic_short(incidents):
    if not incidents:
        return ""
    by_cat = {}
    for inc in incidents:
        by_cat.setdefault(inc["category"], []).append(inc)
    lines = []
    for cat, incs in by_cat.items():
        total_delay = sum(i.get("delay") or 0 for i in incs)
        detail = f" ({len(incs)} incidentes)" if len(incs) > 1 else ""
        if total_delay > 120:
            detail += f" ~{total_delay//60}min demora"
        elif incs[0].get("from"):
            detail += f" en {incs[0]['from']}"
        lines.append(f"- {cat}{detail}")
    return "\n".join(lines[:5])


def has_significant_traffic(incidents):
    if not incidents:
        return False
    for inc in incidents:
        if inc.get("icon") in (1, 8, 11, 14):
            return True
        if (inc.get("delay") or 0) > 300:
            return True
        if inc.get("magnitude", 0) >= 3:
            return True
    return False


# ---------------------------------------------------------------------------
# IA (Claude)
# ---------------------------------------------------------------------------
claude_client = None

SYSTEM_PROMPT = """Sos el asistente de monitoreo de flota de una empresa de transporte en Argentina.
Tu rol: generar alertas de velocidad, responder mensajes, generar resumenes, alertar sobre clima y transito.
Reglas: espanol argentino informal pero profesional. Mensajes cortos. Emojis moderados.
REGLA CRITICA: si te pasan alertas acumuladas del dia, SIEMPRE incluirlas. NUNCA decir "sin incidencias" si hay datos."""


def init_claude():
    global claude_client
    if ANTHROPIC_API_KEY:
        claude_client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY, timeout=30.0)
        print("  Claude IA conectado")
    else:
        print("  Sin ANTHROPIC_API_KEY -- modo basico")


def ia_generar_alerta(plate, speed, limit, zone, lat=None, lng=None):
    exceso = speed - limit

    if not claude_client:
        return {
            "admin":    f"{plate}: {speed:.0f} km/h (lim {limit:.0f}) -- {zone}.",
            "severity": "media",
        }

    historial   = alert_history.get(plate, [])
    hoy_str     = now_local().replace(hour=0, minute=0, second=0).isoformat()
    alertas_hoy = [a for a in historial if a["ts"] > hoy_str]

    clima_ctx = ""
    if lat and lng:
        w = get_weather(lat, lng)
        if w:
            risky, risk_text = is_weather_risky(w)
            if risky:
                clima_ctx += f"\n- CLIMA: {risk_text}"

    trafico_ctx = ""
    if lat and lng and TOMTOM_API_KEY:
        incidents = get_traffic_incidents(lat, lng)
        if incidents and has_significant_traffic(incidents):
            trafico_ctx = f"\n- TRAFICO: {format_traffic_short(incidents)}"

    prompt = f"""Genera alerta de velocidad:
- Patente: {plate}
- Velocidad: {speed:.0f} km/h | Limite: {limit:.0f} km/h | Exceso: {exceso:.0f} km/h
- Zona: {zone} | Alertas hoy: {len(alertas_hoy)}{clima_ctx}{trafico_ctx}

Responder corto, SIN links de Maps.
Responde SOLO con JSON: {{"admin": "...", "severity": "baja|media|alta"}}"""

    try:
        response = claude_client.messages.create(
            model="claude-sonnet-4-20250514",
            max_tokens=200,
            system=SYSTEM_PROMPT,
            messages=[{"role": "user", "content": prompt}],
        )
        text = response.content[0].text.strip().replace("```json", "").replace("```", "").strip()
        return json.loads(text)
    except Exception as e:
        print(f"  IA alerta error: {e}")
        return {"admin": f"{plate}: {speed:.0f} km/h (lim {limit:.0f}) -- {zone}.", "severity": "media"}


def ia_resumen_diario():
    if not daily_events:
        return "Sin eventos hoy. Todo tranquilo."
    if not claude_client:
        return f"Resumen: {len(daily_events)} alertas hoy."

    resumen_data = {}
    for ev in daily_events:
        p = ev.get("vehicle_key", "?")
        if p not in resumen_data:
            resumen_data[p] = {"alertas": 0, "max_speed": 0}
        resumen_data[p]["alertas"] += 1
        spd = ev.get("speed", 0)
        if spd > resumen_data[p]["max_speed"]:
            resumen_data[p]["max_speed"] = spd

    prompt = f"""Resumen diario de flota ({now_local().strftime('%d/%m/%Y')}):
- Total alertas velocidad: {len([e for e in daily_events if e.get('type') != 'ralenti'])}
- Por vehiculo: {json.dumps(resumen_data, ensure_ascii=False)}
- Ralenti: {len([e for e in daily_events if e.get('type') == 'ralenti'])} eventos

Genera resumen ejecutivo max 10 lineas para WhatsApp con emojis moderados."""

    try:
        response = claude_client.messages.create(
            model="claude-sonnet-4-20250514",
            max_tokens=500,
            system=SYSTEM_PROMPT,
            messages=[{"role": "user", "content": prompt}],
        )
        return response.content[0].text.strip()
    except Exception as e:
        print(f"  IA resumen error: {e}")
        return f"Resumen: {len(daily_events)} alertas hoy."


# ---------------------------------------------------------------------------
# ALERTAS ACUMULADAS
# ---------------------------------------------------------------------------
def _construir_bloque_alertas(alertas_por_patente, hora):
    total = sum(d["cantidad"] for d in alertas_por_patente.values())
    if alertas_por_patente:
        lines = [f"*Alertas del Dia* ⚠️ ({total} total desde 00:00 a {hora})"]
        for p, d in sorted(alertas_por_patente.items(), key=lambda x: x[1]["cantidad"], reverse=True):
            lines.append(
                f"  · {p} - {d['cantidad']} alerta{'s' if d['cantidad'] > 1 else ''} "
                f"(max {d['max_vel']:.0f}km/h a las {d['hora']})"
            )
        return "\n".join(lines), total
    return "*Alertas del Dia* ✅\n  · Sin incidencias registradas", 0


def _leer_alertas_csv_hoy():
    alertas_por_patente = {}
    hoy      = now_local().date()
    tz_local = timezone(timedelta(hours=-3))

    if not os.path.exists("logs_alertas_rutasat.csv"):
        return alertas_por_patente

    try:
        with open("logs_alertas_rutasat.csv", "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                try:
                    if row.get("type") == "ralenti":
                        continue
                    ts_raw = row.get("ts", "")
                    if not ts_raw:
                        continue

                    ev_dt = None
                    try:
                        ev_dt = datetime.fromtimestamp(float(ts_raw), tz=tz_local)
                    except Exception:
                        try:
                            ev_dt = datetime.fromisoformat(ts_raw)
                            if ev_dt.tzinfo is None:
                                ev_dt = ev_dt.replace(tzinfo=timezone.utc).astimezone(tz_local)
                            else:
                                ev_dt = ev_dt.astimezone(tz_local)
                        except Exception:
                            continue

                    if ev_dt.date() != hoy:
                        continue

                    p = str(row.get("vehicle_key", "?")).strip().upper() or "?"
                    if p not in alertas_por_patente:
                        alertas_por_patente[p] = {"cantidad": 0, "max_vel": 0, "hora": "?"}

                    alertas_por_patente[p]["cantidad"] += 1
                    spd = float(row.get("speed", 0) or 0)
                    if spd > alertas_por_patente[p]["max_vel"]:
                        alertas_por_patente[p]["max_vel"] = spd
                        alertas_por_patente[p]["hora"]    = ev_dt.strftime("%H:%M")
                except Exception:
                    continue
    except Exception as e:
        print(f"  Error leyendo CSV: {e}")

    return alertas_por_patente


# ---------------------------------------------------------------------------
# REPORTE HORARIO
# ---------------------------------------------------------------------------
def generar_reporte_horario(vehicles):
    """
    Genera reporte SOLO si hay vehículos en movimiento.
    Muestra SOLO los que están en movimiento.
    Ubicación como coordenadas, SIN links de Maps.
    """
    hora  = now_local().strftime("%H:%M")
    fecha = now_local().strftime("%d/%m")

    vehicles = [v for v in vehicles if v["plate"] not in DISPOSITIVOS_EXCLUIDOS]
    total    = len(vehicles)
    ahora_ts = time.time()

    en_movimiento = []
    con_exceso    = []
    parados_count = 0

    for v in vehicles:
        spd         = v["speed_kmh"]
        limit, zone = get_speed_limit(v)

        if spd > MOVEMENT_MIN_SPEED:
            item = {**v, "limit": limit, "zone": zone}
            en_movimiento.append(item)

            if spd > limit:
                if v["plate"] not in speed_exceed_tracking:
                    speed_exceed_tracking[v["plate"]] = ahora_ts
                if (ahora_ts - speed_exceed_tracking[v["plate"]]) >= SPEED_EXCEED_MINUTES * 60:
                    con_exceso.append(item)
            else:
                speed_exceed_tracking.pop(v["plate"], None)
        else:
            parados_count += 1

    if not en_movimiento:
        return None

    ralenti_hora = [
        e for e in daily_events
        if e.get("type") == "ralenti" and (ahora_ts - e.get("ts", 0)) < 3600
    ]

    alertas_por_patente                 = _leer_alertas_csv_hoy()
    alertas_texto_bloque, total_alertas = _construir_bloque_alertas(alertas_por_patente, hora)

    ref           = en_movimiento[0]
    lat_ref       = ref["lat"]
    lng_ref       = ref["lng"]
    w             = get_weather(lat_ref, lng_ref)
    clima_general = format_weather_short(w)

    trafico_general = ""
    if TOMTOM_API_KEY:
        incidents = get_traffic_incidents(lat_ref, lng_ref)
        if incidents and has_significant_traffic(incidents):
            trafico_general = format_traffic_short(incidents)

    msg  = f"*🚛 REPORTE FLOTA - {hora}hs ({fecha})*\n\n"
    msg += "*Estado General*\n"
    msg += f"  · Total: {total} | En movimiento: {len(en_movimiento)} | Parados: {parados_count}\n"
    if clima_general:
        msg += f"  · Clima: {clima_general}\n"
    if trafico_general:
        msg += f"  · Trafico:\n{trafico_general}\n"

    msg += "\n*En Movimiento* 🚗\n"
    for v in en_movimiento:
        exceso_tag = f" ⚠️ excede {v['limit']}km/h" if v["speed_kmh"] > v["limit"] else ""
        msg += f"  · {display_name(v['plate'], v.get('name'))} - {v['speed_kmh']:.0f}km/h{exceso_tag}\n"
        msg += f"    Ubic.: {format_coords(v['lat'], v['lng'])}\n"

    if ralenti_hora:
        msg += "\n*Ralenti última hora*\n"
        for r in ralenti_hora:
            msg += f"  · {display_name(r['vehicle_key'])} - {r['minutes']} min\n"

    msg += "\n" + alertas_texto_bloque + "\n\n"
    msg += "*Estado:* Revisar alertas ⚠️" if total_alertas > 0 else "*Estado:* Operación en curso 👍"
    return msg


# ---------------------------------------------------------------------------
# CIERRE OPERATIVO 18HS
# ---------------------------------------------------------------------------
def generar_reporte_cierre_18(devices, fecha=None):
    """
    Reporte de cierre operativo.
    - Inicio: primer viaje del día
    - Fin: último viaje del día
    - Viajes: cantidad de trips
    - Paradas: stops reales dentro de la jornada (no cuenta la base antes de salir ni al volver)
    """
    fecha = fecha or now_local().date()
    tz_local = timezone(timedelta(hours=-3))

    desde = datetime(fecha.year, fecha.month, fecha.day, 5, 0, 0, tzinfo=tz_local)
    hasta = datetime(fecha.year, fecha.month, fecha.day, 18, 0, 0, tzinfo=tz_local)

    devices_by_plate = build_devices_lookup_by_plate(devices)

    lines = [f"*🚛 CIERRE OPERATIVO 18:00 - {fecha.strftime('%d/%m/%Y')}*", ""]
    total_viajes = 0
    total_paradas = 0
    activos = 0

    for plate in sorted(PATENTES_REPORTE_18):
        device = devices_by_plate.get(plate)

        if not device:
            lines.append(f"· {plate}: no encontrado en RutaSat")
            continue

        trips = get_report_trips(device["id"], desde, hasta)

        if trips:
            trips = sorted(
                trips,
                key=lambda x: str(x.get("startTime") or x.get("deviceTime") or "")
            )

            inicio = hhmm(trips[0].get("startTime"))
            fin    = hhmm(trips[-1].get("endTime"))
            activos += 1

            first_start = parse_dt_local(trips[0].get("startTime"))
            last_end    = parse_dt_local(trips[-1].get("endTime"))

            stops_raw = get_report_stops(device["id"], desde, hasta)
            stops = []

            for s in stops_raw:
                dur_ms = int(s.get("duration", 0) or 0)
                if dur_ms < 5 * 60 * 1000:
                    continue

                s_start = parse_dt_local(s.get("startTime"))
                s_end   = parse_dt_local(s.get("endTime"))
                if not s_start or not s_end:
                    continue

                if first_start and last_end and s_start >= first_start and s_end <= last_end:
                    stops.append(s)

            viajes  = len(trips)
            paradas = len(stops)

            estado = (
                f"· {display_name(plate, device.get('name'))} | inicio {inicio} | fin {fin} | "
                f"viajes {viajes} | paradas {paradas}"
            )
        else:
            viajes  = 0
            paradas = 0
            estado = f"· {display_name(plate, device.get('name'))} | sin viajes registrados"

        total_viajes  += viajes
        total_paradas += paradas
        lines.append(estado)

    lines.append("")
    lines.append(
        f"*Totales:* con actividad {activos}/{len(PATENTES_REPORTE_18)} | "
        f"viajes {total_viajes} | paradas {total_paradas}"
    )

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# WEBHOOK
# ---------------------------------------------------------------------------
def create_webhook_app():
    try:
        from flask import Flask, request as freq
    except ImportError:
        print("Flask no instalado")
        return None

    app = Flask(__name__)

    @app.route("/", methods=["GET", "HEAD"])
    def health():
        return "OK", 200

    @app.route("/webhook", methods=["GET", "HEAD", "POST"])
    def webhook():
        if freq.method in ("GET", "HEAD"):
            return "OK", 200

        from_number = freq.form.get("From", "")
        body        = freq.form.get("Body", "").strip()
        print(f"  MSG from={from_number} body={repr(body)}")

        if from_number:
            wa_session_active[from_number] = time.time()

        if not body:
            return "OK", 200

        is_admin  = from_number in set(get_admin_numbers())
        twilio_cl = Client(TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN)

        if is_admin:
            body_lower = body.lower().strip()
            try:
                devices   = get_devices()
                positions = get_positions()
                vehicles  = build_vehicle_list(devices, positions)
            except Exception as e:
                devices = []
                vehicles = []
                print(f"  Error GPS: {e}")

            if any(x in body_lower for x in ["reporte", "estado", "flota"]):
                respuesta = generar_reporte_horario(vehicles) or "Sin vehículos en movimiento en este momento."
            elif any(x in body_lower for x in ["cierre", "jornada", "18hs"]):
                respuesta = generar_reporte_cierre_18(devices, now_local().date())
            elif "resumen" in body_lower:
                respuesta = ia_resumen_diario()
            elif any(x in body_lower for x in ["clima", "tiempo", "lluvia"]):
                w = get_weather(-32.16, -64.10)
                respuesta = format_weather_short(w) if w else "Sin datos de clima"
            elif any(x in body_lower for x in ["trafico", "transito"]):
                incidents = get_traffic_incidents(-32.16, -64.10)
                if incidents:
                    respuesta = format_traffic_short(incidents) or "Sin incidentes de trafico"
                else:
                    respuesta = "Sin datos de trafico (verificar TOMTOM_API_KEY)"
            elif any(x in body_lower for x in ["ayuda", "comandos"]):
                respuesta = (
                    "Comandos disponibles:\n"
                    "- reporte: muestra solo los vehículos en movimiento\n"
                    "- cierre / jornada / 18hs: inicio, fin, viajes y paradas\n"
                    "- resumen: resumen del día\n"
                    "- clima: condiciones actuales\n"
                    "- trafico: incidentes viales\n"
                    "- ayuda: esta lista"
                )
            else:
                respuesta = (
                    "Mensaje recibido. Comandos: reporte, cierre, resumen, clima, trafico, ayuda"
                )

            try:
                send_whatsapp(twilio_cl, from_number, respuesta)
            except Exception as e:
                print(f"  Error enviando respuesta WA: {e}")
                try:
                    send_whatsapp(
                        twilio_cl,
                        from_number,
                        "No pude enviar el mensaje completo por WhatsApp. El reporte salió demasiado largo."
                    )
                except Exception as e2:
                    print(f"  Error enviando fallback WA: {e2}")

            return "OK", 200

        try:
            send_to_admins(twilio_cl, f"Mensaje de {from_number}: {body}")
            send_whatsapp(twilio_cl, from_number, "Recibido. Tu mensaje fue registrado.")
        except Exception as e:
            print(f"  Error webhook no-admin: {e}")

        return "OK", 200

    return app


# ---------------------------------------------------------------------------
# LOOP PRINCIPAL
# ---------------------------------------------------------------------------
def main():
    if not RUTASAT_EMAIL or not RUTASAT_PASSWORD:
        raise SystemExit("Faltan RUTASAT_EMAIL / RUTASAT_PASSWORD en .envvars")
    if not TWILIO_ACCOUNT_SID or not TWILIO_AUTH_TOKEN or not TWILIO_WHATSAPP_FROM:
        raise SystemExit("Faltan variables de Twilio en .envvars")
    if not ADMIN_WHATSAPP:
        raise SystemExit("Falta ADMIN_WHATSAPP en .envvars")

    init_claude()
    twilio = Client(TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN)

    last_alert_ts       = {}
    last_summary_date   = None
    last_cierre_18_date = None

    print("\nAgente RutaSat v1.6 corriendo")
    print(f"  Poll: {POLL_SECONDS}s | Ruta: {LIMITE_RUTA}km/h | Urbano: {LIMITE_URBANO}km/h | Ruta-110: 110km/h")
    if PATENTES_110:
        print(f"  Vehiculos 110km/h - Patentes: {', '.join(sorted(PATENTES_110))}")
    print(f"  Admins: {', '.join(get_admin_numbers())}")
    print(f"  IA Claude: {'Activada' if claude_client else 'Modo basico'}")
    print("  Clima: Open-Meteo (gratis, sin API key)")
    print(f"  Trafico TomTom: {'Activado' if TOMTOM_API_KEY else 'No configurado (opcional)'}")
    print(f"  Template WA: {'Configurado' if TWILIO_CONTENT_SID else 'No configurado'}")
    print(f"  MAX_WA_BODY: {MAX_WA_BODY}")
    print(f"  Reporte cierre 18hs: {len(PATENTES_REPORTE_18)} patentes")
    print(f"  Reporte horario diurno: solo si hay movimiento > {MOVEMENT_MIN_SPEED} km/h")
    print(f"  Uso fuera de horario: {AFTER_HOURS_START} a {AFTER_HOURS_END}")
    print(f"  Ralenti excluido para: {', '.join(sorted(RALENTI_EXCLUIDOS_MATCH))}")
    print()

    global last_hourly_report

    while True:
        try:
            print(f"  [{now_local().strftime('%H:%M')}] Poll...", flush=True)
            hora_local = now_local()
            today      = hora_local.date()

            # Resumen diario a las 21hs
            if hora_local.hour == 21 and last_summary_date != today:
                print("  Generando resumen diario...")
                try:
                    resumen = ia_resumen_diario()
                    send_to_admins(twilio, resumen)
                    last_summary_date = today
                    daily_events.clear()
                    print("  Resumen enviado")
                except Exception as e:
                    print(f"  Error resumen: {e}")

            # Obtener datos GPS
            try:
                devices   = get_devices()
                positions = get_positions()
                vehicles  = build_vehicle_list(devices, positions)
                print(f"  Vehiculos: {len(vehicles)}", flush=True)
            except Exception as e:
                print(f"  Error GPS: {e}")
                time.sleep(30)
                continue

            # CIERRE OPERATIVO 18HS
            if hora_local.hour >= 18 and last_cierre_18_date != today:
                print("  Generando cierre operativo 18hs...")
                try:
                    cierre_18 = generar_reporte_cierre_18(devices, today)
                    send_to_admins(twilio, cierre_18)
                    last_cierre_18_date = today
                    print("  Cierre 18hs enviado")
                except Exception as e:
                    print(f"  Error cierre 18hs: {e}")

            # REPORTE HORARIO SOLO ANTES DE 20:30 Y SOLO SI HAY MOVIMIENTO
            ahora = time.time()
            if not is_after_hours(hora_local) and (ahora - last_hourly_report >= 3600):
                print("  Evaluando reporte horario diurno...")
                try:
                    reporte = generar_reporte_horario(vehicles)
                    if reporte:
                        send_to_admins(twilio, reporte)
                        print("  Reporte enviado")
                    else:
                        print("  Reporte omitido: no hay vehículos en movimiento")
                    last_hourly_report = ahora
                except Exception as e:
                    print(f"  Error reporte: {e}")
                    last_hourly_report = ahora

            # Monitoreo por vehiculo
            ahora_ts = time.time()
            for v in vehicles:
                try:
                    plate    = v["plate"]
                    lat      = v["lat"]
                    lng      = v["lng"]
                    speed    = v["speed_kmh"]
                    ignition = v["ignition"]
                    dname    = display_name(plate, v.get("name"))

                    # -------------------------------------------------------
                    # USO FUERA DE HORARIO: si empieza a moverse después de 20:30
                    # -------------------------------------------------------
                    if is_after_hours(hora_local):
                        if speed > MOVEMENT_MIN_SPEED:
                            if not after_hours_motion_state.get(plate):
                                after_hours_motion_state[plate] = True
                                after_msg = (
                                    f"🚨 Uso fuera de horario\n"
                                    f"· {dname}\n"
                                    f"· Hora: {hora_local.strftime('%H:%M')}\n"
                                    f"· Velocidad: {speed:.0f} km/h\n"
                                    f"· Ubic.: {format_coords(lat, lng)}"
                                )
                                send_to_admins(twilio, after_msg)
                                print(f"  USO FUERA DE HORARIO: {dname} a {speed:.0f} km/h")
                        else:
                            after_hours_motion_state.pop(plate, None)
                    else:
                        after_hours_motion_state.pop(plate, None)

                    # RALENTI (excluyendo solo A241VOY)
                    if ignition and speed <= 2 and not is_idle_excluded(v):
                        if plate not in idle_tracking:
                            idle_tracking[plate] = ahora_ts
                        else:
                            minutos_idle = (ahora_ts - idle_tracking[plate]) / 60
                            if minutos_idle >= IDLE_MINUTES and ahora_ts - idle_alerted.get(plate, 0) > 1800:
                                idle_alerted[plate] = ahora_ts
                                idle_msg = (
                                    f"⚠️ RALENTI {dname}: motor encendido y parado "
                                    f"hace {minutos_idle:.0f} min."
                                )
                                if claude_client:
                                    try:
                                        resp = claude_client.messages.create(
                                            model="claude-sonnet-4-20250514",
                                            max_tokens=150,
                                            system=SYSTEM_PROMPT,
                                            messages=[{"role": "user", "content":
                                                f"Alerta ralenti: {dname} motor encendido "
                                                f"parado {minutos_idle:.0f} min. 2 lineas max. SIN Maps."}],
                                        )
                                        idle_msg = resp.content[0].text.strip()
                                    except Exception:
                                        pass

                                send_to_admins(twilio, idle_msg)
                                daily_events.append({
                                    "vehicle_key": plate,
                                    "type": "ralenti",
                                    "minutes": f"{minutos_idle:.0f}",
                                    "lat": lat,
                                    "lng": lng,
                                    "ts": ahora_ts,
                                })
                                log_event({
                                    "ts": ahora_ts,
                                    "vehicle_key": plate,
                                    "type": "ralenti",
                                    "minutes": f"{minutos_idle:.0f}",
                                    "speed": 0,
                                    "limit": 0,
                                    "zone": "",
                                })
                                print(f"  RALENTI: {dname} - {minutos_idle:.0f} min")
                    else:
                        idle_tracking.pop(plate, None)

                    # VELOCIDAD — usar get_speed_limit()
                    limit, zone = get_speed_limit(v)

                    if speed <= limit:
                        speed_exceed_tracking.pop(plate, None)
                        continue

                    if ahora_ts - last_alert_ts.get(plate, 0) < 300:
                        continue

                    last_alert_ts[plate] = ahora_ts

                    print(f"  {dname} -> {speed:.0f} km/h (lim {limit}, {zone})")
                    mensajes = ia_generar_alerta(dname, speed, limit, zone, lat, lng)

                    # SIN Maps para evitar spam / mensajes partidos
                    send_to_admins(twilio, mensajes["admin"])

                    alert_history.setdefault(plate, []).append({"ts": now_iso(), "speed": speed})
                    daily_events.append({
                        "vehicle_key": plate,
                        "speed": speed,
                        "limit": limit,
                        "zone": zone,
                        "severity": mensajes.get("severity", "media"),
                        "ts": ahora_ts,
                    })
                    log_event({
                        "ts": ahora_ts,
                        "vehicle_key": plate,
                        "type": "velocidad",
                        "speed": f"{speed:.1f}",
                        "limit": limit,
                        "zone": zone,
                    })
                    print(f"  Alerta enviada ({mensajes.get('severity', '?')})")

                except Exception as e:
                    print(f"  Error procesando {v.get('plate', '?')}: {e}")
                    continue

            time.sleep(POLL_SECONDS)

        except Exception as e:
            print(f"[{now_iso()}] ERROR loop: {e}")
            traceback.print_exc()
            time.sleep(30)


# ---------------------------------------------------------------------------
# ENTRY POINT
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    import threading

    port = int(os.getenv("PORT", "5000"))

    def watchdog():
        while True:
            t = threading.Thread(target=main, daemon=True)
            t.start()
            print("Agente iniciado en background")
            t.join()
            print("WATCHDOG: reiniciando en 10s...")
            time.sleep(10)

    threading.Thread(target=watchdog, daemon=True).start()

    app = create_webhook_app()
    if app:
        print(f"Webhook activo en puerto {port}")
        app.run(host="0.0.0.0", port=port, debug=False, threaded=True, use_reloader=False)
    else:
        main()
