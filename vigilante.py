"""
Vigilante Sistema Maestro (versión corregida)

Cambios principales respecto a la versión anterior:
  - Se eliminaron las funciones duplicadas y el hilo actualizador redundante.
  - Un solo disparador automático (hilo interno) + lock global para todo scrape.
  - Guardado atómico del JSON y error explícito si el JSON está corrupto.
  - Comparación de departamentos normalizada (sin tildes/mayúsculas/puntuación).
  - El scrape reporta si fue COMPLETO; solo se borran plazas si lo fue.
  - Reintentos de red, parseo tolerante y detección de detalles sin expandir.
  - Chequeo barato del mapa cada ciclo; scrape completo solo si cambió el mapa
    o cada INTERVALO_SCRAPE_COMPLETO segundos.
  - Primera ejecución (base vacía) no inunda Telegram con "nuevas".
  - Endpoints destructivos protegidos con ADMIN_KEY.
  - Webhook con secret_token real y lista opcional de chats permitidos.
"""
from flask import Flask, request
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import os
import re
import json
import html
import hmac
import shutil
import threading
import time
import traceback
import unicodedata
from datetime import datetime, timedelta
from collections import defaultdict, Counter
from bs4 import BeautifulSoup
import xml.etree.ElementTree as ET
from zoneinfo import ZoneInfo

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 10 * 1024 * 1024  # 10 MB

# ============================================================
# CONFIGURACIÓN
# ============================================================
TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")

# Clave para endpoints que modifican datos. Si no se define, esos endpoints
# quedan DESHABILITADOS (más seguro que dejarlos abiertos).
ADMIN_KEY = os.environ.get("ADMIN_KEY", "")

# Chats que pueden usar "Actualizar"/"Menú". Vacío = cualquiera (comportamiento anterior).
_env_chats = {c.strip() for c in os.environ.get("ALLOWED_CHAT_IDS", "").split(",") if c.strip()}
CHATS_PERMITIDOS = (_env_chats | {str(TELEGRAM_CHAT_ID)}) if _env_chats else None

URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ZONA_COLOMBIA = ZoneInfo("America/Bogota")

# En Render: monta un Persistent Disk (p. ej. en /data) y define DATA_DIR=/data
DATA_DIR = os.environ.get("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)

def _ruta(nombre):
    return os.path.join(DATA_DIR, nombre)

ARCHIVO_DATOS = _ruta("plazas.json")
ARCHIVO_ESTADO = _ruta("total_mapa.json")
ARCHIVO_ULTIMA_ACTUALIZACION = _ruta("ultima_actualizacion_completa.json")
ARCHIVO_LOCK_PROCESO = _ruta("vigilante.lock")

INTERVALO_VIGILANTE_SEGUNDOS = int(os.environ.get("INTERVALO_VIGILANTE_SEGUNDOS", 60))
INTERVALO_SCRAPE_COMPLETO = int(os.environ.get("INTERVALO_SCRAPE_COMPLETO", 300))
MIN_SEGUNDOS_ENTRE_CHEQUEOS = 30   # límite para /check
MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6
MAX_CLICS_DETALLE = 50

HEADERS_AJAX = {
    "accept": "application/xml, text/xml, */*; q=0.01",
    "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
    "faces-request": "partial/ajax",
    "x-requested-with": "XMLHttpRequest",
    "User-Agent": "Mozilla/5.0",
}

# Locks
lock_json = threading.RLock()                 # acceso al archivo
lock_ejecucion_vigilante = threading.Lock()   # UN solo scrape a la vez (todo el proceso)
lock_estado_vigilante = threading.Lock()
lock_estados_menu = threading.Lock()

estado_vigilante_automatico = {
    "ultimo_inicio_ts": 0.0,
    "ultima_ejecucion": None,
    "ultimo_resultado": None,
    "ejecuciones": 0,
}
estados_menu_chat = {}
_ultima_alerta_error_ts = 0.0

# ============================================================
# UTILIDADES
# ============================================================

def norm(s):
    """Normaliza nombres: sin tildes, minúsculas y solo letras/números."""
    s = unicodedata.normalize("NFD", str(s or "").lower())
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return re.sub(r"[^a-z0-9]", "", s)

def crear_sesion():
    """Sesión con reintentos automáticos ante fallos de red / 5xx."""
    s = requests.Session()
    retry = Retry(
        total=3, backoff_factor=1,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset(["GET", "POST"]),
    )
    adapter = HTTPAdapter(max_retries=retry)
    s.mount("https://", adapter)
    s.mount("http://", adapter)
    s.headers.update({"User-Agent": "Mozilla/5.0"})
    return s

# ========== MAPEO DE DEPARTAMENTOS (respaldo; se prefiere leer los códigos de la página) ==========
DEPARTAMENTOS_CODIGOS = {
    "amazonas": "91", "antioquia": "05", "arauca": "81", "atlántico": "08",
    "bogotá": "11", "bogotá d.c": "11", "bolívar": "13", "boyacá": "15",
    "caldas": "17", "caquetá": "18", "casanare": "85", "cauca": "19",
    "cesar": "20", "chocó": "27", "córdoba": "23", "cundinamarca": "25",
    "guainía": "94", "guaviare": "95", "huila": "41", "la guajira": "44",
    "magdalena": "47", "meta": "50", "nariño": "52", "norte de santander": "54",
    "putumayo": "86", "quindío": "63", "risaralda": "66", "san andrés": "88",
    "santander": "68", "sucre": "70", "tolima": "73", "valle del cauca": "76",
    "vaupés": "97", "vichada": "99",
}
DEPARTAMENTOS_CODIGOS_NORM = {norm(k): v for k, v in DEPARTAMENTOS_CODIGOS.items()}

# Cache de códigos leídos del <select> de la página (se refresca cada hora)
_cache_codigos = {"ts": 0.0, "codigos": {}}

def extraer_codigos_departamentos(texto_html):
    codigos = {}
    try:
        soup = BeautifulSoup(texto_html, "html.parser")
        sel = soup.find("select", id="form-busqueda:idInputDepartamento_input")
        if sel:
            for op in sel.find_all("option"):
                val = (op.get("value") or "").strip()
                nombre = op.get_text(strip=True)
                if val and nombre:
                    codigos[norm(nombre)] = val
    except Exception as e:
        print(f"⚠️ No se pudieron leer los códigos de departamento de la página: {e}")
    return codigos

def resolver_codigo(nombre, codigos_pagina):
    n = norm(nombre)
    if n in codigos_pagina:
        return codigos_pagina[n]
    if n in DEPARTAMENTOS_CODIGOS_NORM:
        return DEPARTAMENTOS_CODIGOS_NORM[n]
    for k, v in DEPARTAMENTOS_CODIGOS_NORM.items():
        if n and (n in k or k in n):
            return v
    return None

# ========== ABREVIATURAS DE ÁREAS ==========
AREA_ABREVIATURAS = {
    "sin asignación directa": "Sin Asignación",
    "ciencias económicas y políticas": "C. Económicas",
    "ciencias naturales física": "C. Naturales - Física",
    "ciencias naturales química": "C. Naturales - Química",
    "ciencias naturales y educación ambiental": "C. Naturales",
    "ciencias sociales": "C. Sociales",
    "educación artística - artes escénicas": "Artes Escénicas",
    "educación artística - artes plásticas": "Artes Plásticas",
    "educación artística – danzas": "Danzas",
    "educación artística – música": "Música",
    "educación artística - danzas (programa pta)": "Danzas - PTA",
    "educación artística - literatura (programa pta)": "Literatura - PTA",
    "educación artística - música (programa pta)": "Música - PTA",
    "educación ética y en valores": "Ética y Valores",
    "educación física, recreación y deporte": "Ed. Física",
    "educación religiosa": "Religión",
    "filosofía": "Filosofía",
    "humanidades y lengua castellana": "Hum. y Len. Castellana",
    "idioma extranjero inglés": "Inglés",
    "matemáticas": "Matemáticas",
    "tecnología e informática": "Tecno-Infor",
    "áreas de apoyo para educación especial": "Apoyo Ed. Especial",
    "orientadores": "Orientadores",
    "preescolar": "Preescolar",
    "primaria": "Primaria",
}

def abreviar_area(area):
    if not area:
        return "Sin área"
    return AREA_ABREVIATURAS.get(area.lower().strip(), area)

# ============================================================
# CARGA / GUARDADO (atómico)
# ============================================================

def _guardar_json_atomico(ruta, objeto):
    tmp = ruta + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(objeto, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, ruta)

def cargar_datos_anteriores():
    """
    [] si el archivo no existe. Si existe pero está corrupto, guarda un
    respaldo y LANZA error (así no se interpreta como 'base vacía' y no se
    dispara una avalancha de 'plazas nuevas').
    """
    with lock_json:
        if not os.path.exists(ARCHIVO_DATOS):
            return []
        try:
            with open(ARCHIVO_DATOS, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, list):
                raise ValueError("el JSON no es una lista")
            return data
        except Exception as e:
            respaldo = ARCHIVO_DATOS + ".corrupto"
            try:
                shutil.copy(ARCHIVO_DATOS, respaldo)
            except Exception:
                pass
            raise RuntimeError(f"plazas.json ilegible ({e}). Respaldo en {respaldo}") from e

def guardar_datos_actuales(plazas, permitir_vacio=False):
    with lock_json:
        if not plazas and not permitir_vacio:
            print("⚠️ Se intentó guardar una lista vacía de plazas. No se sobrescribió el archivo.")
            return
        _guardar_json_atomico(ARCHIVO_DATOS, plazas)

def cargar_estado_mapa():
    try:
        with open(ARCHIVO_ESTADO, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def guardar_estado_mapa(estado):
    _guardar_json_atomico(ARCHIVO_ESTADO, estado)

def guardar_ultima_actualizacion_completa(fecha):
    _guardar_json_atomico(ARCHIVO_ULTIMA_ACTUALIZACION, {"ultima": fecha.isoformat()})

def cargar_ultima_actualizacion_completa():
    try:
        with open(ARCHIVO_ULTIMA_ACTUALIZACION, "r", encoding="utf-8") as f:
            fecha = datetime.fromisoformat(json.load(f)["ultima"])
        if fecha.tzinfo is None:
            fecha = fecha.replace(tzinfo=ZONA_COLOMBIA)
        return fecha
    except Exception:
        return None

# ============================================================
# SCRAPING
# ============================================================
PATRON_MARCADOR = re.compile(r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'")

def obtener_conteo_mapa(session=None):
    """Cuenta marcadores (plazas) por departamento según el mapa en vivo."""
    s = session or crear_sesion()
    r = s.get(URL_PAGINA, timeout=30)
    r.raise_for_status()
    contador = Counter()
    for t in PATRON_MARCADOR.findall(r.text):
        contador[t.split(" - ")[0].strip()] += 1
    return contador

def obtener_total_plazas_mapa():
    return sum(obtener_conteo_mapa().values())

def iniciar_sesion_scraping():
    session = crear_sesion()
    r = session.get(URL_PAGINA, timeout=30)
    r.raise_for_status()
    m = re.search(r'javax\.faces\.ViewState" value="([^"]+)"', r.text)
    if not m:
        raise RuntimeError("No se pudo obtener el ViewState inicial")

    ahora = time.time()
    if not _cache_codigos["codigos"] or ahora - _cache_codigos["ts"] > 3600:
        codigos = extraer_codigos_departamentos(r.text)
        if codigos:
            _cache_codigos["codigos"] = codigos
            _cache_codigos["ts"] = ahora
    return session, m.group(1), _cache_codigos["codigos"]

def extraer_actualizaciones(xml_texto):
    resultado = {"html": "", "viewstate": None}
    try:
        root = ET.fromstring(xml_texto)
    except ET.ParseError:
        return resultado
    partes = []
    for update in root.iter("update"):
        update_id = update.get("id") or ""
        contenido = update.text or ""
        if update_id == "javax.faces.ViewState":
            resultado["viewstate"] = contenido.strip()
        else:
            partes.append(contenido)
    resultado["html"] = "\n".join(partes)
    return resultado

def extraer_campo(soup, patron):
    etiqueta = soup.find("label", string=re.compile(patron))
    if etiqueta:
        return re.sub(patron, "", etiqueta.get_text(strip=True), count=1).strip()
    return None

def parsear_vacantes(html_fragmento):
    soup = BeautifulSoup(html_fragmento or "", "html.parser")
    vacantes = []
    for panel in soup.select("div.vacante"):
        cargo = extraer_campo(panel, r"Cargo")
        postulados_texto = extraer_campo(panel, r"Postulados:")
        m = re.search(r"\d+", postulados_texto or "")
        postulados = int(m.group()) if m else 0
        tipo = extraer_campo(panel, r"Tipo Priorización:")
        cierre = extraer_campo(panel, r"Cierre vacante:")
        cierre = re.sub(r"\s+", " ", cierre).strip() if cierre else ""
        area = extraer_campo(panel, r"Área:")
        secretaria = extraer_campo(panel, r"Secretaría de Educación:")

        zonas = panel.find_all("label", string=re.compile(r"Zona:"))
        zona_geografica = zonas[0].get_text(strip=True).replace("Zona:", "").strip() if zonas else "Sin zona"
        zona_tipo = zonas[1].get_text(strip=True).replace("Zona:", "").strip().capitalize() if len(zonas) > 1 else "Sin tipo"

        departamento = extraer_campo(panel, r"Departamento:")
        municipio = extraer_campo(panel, r"Municipio:")

        # OJO: mismo formato de ID que antes, para no romper el JSON ya guardado.
        id_plaza = f"{departamento}|{area}|{zona_geografica}|{municipio}|{cierre}|{secretaria}|{cargo}|{tipo}"
        id_plaza = id_plaza.lower().replace(" ", "_")

        vacantes.append({
            "id": id_plaza,
            "area": area or "Sin área",
            "secretaria": secretaria or "Sin secretaría",
            "zona": zona_geografica,
            "zona_tipo": zona_tipo,
            "departamento": departamento or "Sin departamento",
            "municipio": municipio or "Sin municipio",
            "tipo_priorizacion": tipo or "Sin tipo",
            "cierre": cierre,
            "postulados": postulados,
            "cargo": cargo or "Sin cargo",
        })
    return vacantes

def expandir_todos_detalles(session, viewstate, html_actual):
    """
    Hace clic en todos los "Ver detalle". Devuelve (html, viewstate, ok).
    ok=False si algo falló y quedaron detalles sin expandir.
    """
    soup = BeautifulSoup(html_actual, "html.parser")
    for _ in range(MAX_CLICS_DETALLE):
        enlaces = [a for a in soup.select("div.vacante a.ui-commandlink")
                   if a.get_text(strip=True) == "Ver detalle"]
        if not enlaces:
            return html_actual, viewstate, True

        source_id = enlaces[0].get("id")
        if not source_id:
            return html_actual, viewstate, False

        data = {
            "javax.faces.partial.ajax": "true",
            "javax.faces.source": source_id,
            "javax.faces.partial.execute": "@all",
            "javax.faces.partial.render": "form-busqueda:tabla-vacantes",
            "javax.faces.behavior.event": "click",
            "javax.faces.partial.event": "click",
            source_id: source_id,
            "form-busqueda": "form-busqueda",
            "javax.faces.ViewState": viewstate,
        }
        formulario = soup.find("form", id="form-busqueda")
        if formulario:
            for inp in formulario.find_all("input", type="hidden"):
                name = inp.get("name")
                if name and name not in data:
                    data[name] = inp.get("value", "")

        response = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
        response.raise_for_status()
        resultado = extraer_actualizaciones(response.text)
        if resultado["viewstate"]:
            viewstate = resultado["viewstate"]
        if not resultado["html"]:
            return html_actual, viewstate, False
        html_actual = resultado["html"]
        soup = BeautifulSoup(html_actual, "html.parser")

    return html_actual, viewstate, False  # se agotaron los intentos

def desambiguar_ids(vacantes):
    """Agrega sufijos a IDs duplicados (plazas gemelas), según orden de aparición."""
    conteo_total = Counter(v["id"] for v in vacantes)
    contador_visto = defaultdict(int)
    for v in vacantes:
        id_base = v["id"]
        if conteo_total[id_base] > 1:
            contador_visto[id_base] += 1
            v["id"] = f"{id_base}__{contador_visto[id_base]}"
    return vacantes

def _campos_filtro(viewstate, codigo_departamento):
    return {
        "form-busqueda": "form-busqueda",
        "javax.faces.ViewState": viewstate,
        "form-busqueda:idInputSecretaria_focus": "",
        "form-busqueda:idInputSecretaria_input": "",
        "form-busqueda:idInputDepartamento_focus": "",
        "form-busqueda:idInputDepartamento_input": codigo_departamento,
        "form-busqueda:idInputEstablecimiento_filter": "",
        "form-busqueda:idInputArea_focus": "",
        "form-busqueda:idInputArea_input": "",
        "form-busqueda:idInputTipoPonderado_focus": "",
        "form-busqueda:idInputTipoPonderado_input": "",
        "form-busqueda:zoom-actual": "5",
        "form-busqueda:lat-seleccionada": "",
        "form-busqueda:lon-seleccionada": "",
        "form-busqueda:info-punto": "",
    }

def cambiar_filtro_departamento(session, viewstate, codigo_departamento):
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:idInputDepartamento",
        "javax.faces.partial.execute": "@all",
        "javax.faces.partial.render": "accordion",
        "javax.faces.behavior.event": "change",
        "javax.faces.partial.event": "change",
        "form-busqueda:tabla-vacantes_rppDD": str(FILAS_POR_PAGINA),
    }
    data.update(_campos_filtro(viewstate, codigo_departamento))
    r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
    r.raise_for_status()
    resultado = extraer_actualizaciones(r.text)
    return resultado["html"], (resultado["viewstate"] or viewstate)

def pedir_pagina_filtrada(session, viewstate, first, rows, codigo_departamento):
    """Devuelve (html_con_detalles, viewstate, ok)."""
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:tabla-vacantes",
        "javax.faces.partial.execute": "form-busqueda:tabla-vacantes",
        "javax.faces.partial.render": "form-busqueda:tabla-vacantes",
        "form-busqueda:tabla-vacantes": "form-busqueda:tabla-vacantes",
        "form-busqueda:tabla-vacantes_pagination": "true",
        "form-busqueda:tabla-vacantes_first": str(first),
        "form-busqueda:tabla-vacantes_rows": str(rows),
        "form-busqueda:tabla-vacantes_rppDD": str(rows),
    }
    data.update(_campos_filtro(viewstate, codigo_departamento))
    r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
    r.raise_for_status()
    resultado = extraer_actualizaciones(r.text)
    nuevo_viewstate = resultado["viewstate"] or viewstate
    html_frag = resultado["html"]

    try:
        return expandir_todos_detalles(session, nuevo_viewstate, html_frag)
    except Exception as e:
        print(f"⚠️ Error al expandir detalles (página {first // rows + 1}): {e}")
        return html_frag, nuevo_viewstate, False

def obtener_vacantes_por_departamento(nombre_departamento):
    """
    Devuelve (plazas, completo). `completo` es True solo si TODAS las páginas
    se leyeron y expandieron sin errores y las plazas son del departamento pedido.
    """
    session, viewstate, codigos_pagina = iniciar_sesion_scraping()
    codigo = resolver_codigo(nombre_departamento, codigos_pagina)
    if not codigo:
        raise ValueError(f"Departamento '{nombre_departamento}' no encontrado en el mapeo")

    _, viewstate = cambiar_filtro_departamento(session, viewstate, codigo)

    todas = []
    completo = True
    termino_limpio = False
    first = 0
    for _ in range(MAX_PAGINAS):
        try:
            html_frag, viewstate, ok = pedir_pagina_filtrada(session, viewstate, first, FILAS_POR_PAGINA, codigo)
        except Exception as e:
            print(f"⚠️ Error leyendo página {first // FILAS_POR_PAGINA + 1} de {nombre_departamento}: {e}")
            completo = False
            break
        if not ok:
            completo = False
        vacantes = parsear_vacantes(html_frag)
        if not vacantes:
            termino_limpio = True
            break
        todas.extend(vacantes)
        first += FILAS_POR_PAGINA
        if len(vacantes) < FILAS_POR_PAGINA:
            termino_limpio = True
            break

    if not termino_limpio:
        completo = False
    if not todas:
        completo = False   # un departamento del mapa siempre tiene >= 1 plaza

    validas = []
    nd = norm(nombre_departamento)
    for v in todas:
        if v["departamento"] == "Sin departamento" or v["municipio"] == "Sin municipio":
            completo = False     # detalle sin expandir: ID/datos poco confiables
            continue
        if norm(v["departamento"]) != nd:
            print(f"⚠️ Plaza de '{v['departamento']}' devuelta al pedir '{nombre_departamento}' (¿código incorrecto?)")
            completo = False
            continue
        validas.append(v)

    return desambiguar_ids(validas), completo

# ============================================================
# RECONCILIACIÓN
# ============================================================

def reconciliar_departamento(plazas_bd, scrapeadas, departamento, completo, cantidad_esperada=None):
    """
    Agrega/actualiza siempre. Borra las plazas del departamento que ya no
    aparecen SOLO si el scrape fue completo (y trajo al menos las esperadas
    según el mapa). Devuelve (lista, ids_nuevas).
    """
    por_id = {p["id"]: dict(p) for p in plazas_bd}
    nd = norm(departamento)

    puede_borrar = completo and (cantidad_esperada is None or len(scrapeadas) >= cantidad_esperada)
    if puede_borrar:
        ids_scrap = {p["id"] for p in scrapeadas}
        for pid in [pid for pid, p in por_id.items()
                    if norm(p.get("departamento")) == nd and pid not in ids_scrap]:
            del por_id[pid]
    else:
        print(f"⚠️ {departamento}: scrape incompleto ({len(scrapeadas)} de "
              f"{cantidad_esperada if cantidad_esperada is not None else '?'}); solo se agrega/actualiza.")

    ids_nuevas = set()
    for p in scrapeadas:
        if p["id"] in por_id:
            por_id[p["id"]].update(p)
        else:
            por_id[p["id"]] = dict(p)
            ids_nuevas.add(p["id"])
    return list(por_id.values()), ids_nuevas

# ========== PLAZAS VENCIDAS ==========

def parsear_fecha_cierre(cierre_texto):
    if not cierre_texto:
        return None
    try:
        fecha_naive = datetime.strptime(cierre_texto.strip(), "%d/%m/%Y a las %H:%M")
        return fecha_naive.replace(tzinfo=ZONA_COLOMBIA)
    except ValueError:
        return None

def limpiar_plazas_vencidas(plazas):
    ahora = datetime.now(ZONA_COLOMBIA)
    vigentes, vencidas = [], []
    for p in plazas:
        fecha_cierre = parsear_fecha_cierre(p.get("cierre"))
        if fecha_cierre and fecha_cierre <= ahora:
            vencidas.append(p)
        else:
            vigentes.append(p)
    return vigentes, vencidas

# ============================================================
# CAMBIOS Y MENSAJES
# ============================================================

def detectar_cambios_completos(plazas_actuales, plazas_anteriores):
    anteriores = {p["id"]: p for p in plazas_anteriores}
    actuales = {p["id"]: p for p in plazas_actuales}
    nuevas, eliminadas, actualizadas = [], [], []

    for pid, p in actuales.items():
        if pid not in anteriores:
            nuevas.append(p)
        elif p.get("postulados") != anteriores[pid].get("postulados"):
            actualizadas.append({
                "id": pid,
                "departamento": p.get("departamento"),
                "area": p.get("area"),
                "municipio": p.get("municipio"),
                "postulados_anterior": anteriores[pid].get("postulados"),
                "postulados_actual": p.get("postulados"),
            })
    for pid, p in anteriores.items():
        if pid not in actuales:
            eliminadas.append(p)

    return {
        "nuevas": nuevas, "eliminadas": eliminadas, "actualizadas": actualizadas,
        "total_nuevas": len(nuevas), "total_eliminadas": len(eliminadas),
        "total_actualizadas": len(actualizadas),
    }

def contar_plazas_por_activacion(plazas):
    """(hoy, ayer): plazas cuya activación (cierre - 24h) cae hoy / ayer."""
    hoy = datetime.now(ZONA_COLOMBIA).date()
    ayer = hoy - timedelta(days=1)
    c_hoy = c_ayer = 0
    for p in plazas:
        fecha_cierre = parsear_fecha_cierre(p.get("cierre"))
        if fecha_cierre:
            activacion = (fecha_cierre - timedelta(days=1)).date()
            if activacion == hoy:
                c_hoy += 1
            elif activacion == ayer:
                c_ayer += 1
    return c_hoy, c_ayer

def _linea_plaza(p, marca="", flecha=""):
    area = html.escape(abreviar_area(p.get("area")))
    muni = html.escape(str(p.get("municipio", "?")))
    zona = html.escape(str(p.get("zona_tipo", "?")))
    return f"  • {area} ({muni} - {zona}){marca}{flecha} – {p.get('postulados', 0)} postulados"

def _bloque_por_departamento(plazas, ids_nuevas=None, cambios_post=None):
    ids_nuevas = ids_nuevas or set()
    cambios_post = cambios_post or {}
    deptos = defaultdict(list)
    for p in plazas:
        deptos[p.get("departamento", "Sin departamento")].append(p)

    lineas = []
    for depto in sorted(deptos.keys()):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x.get("area", "")):
            marca = " 🆕" if p["id"] in ids_nuevas else ""
            flecha = ""
            if p["id"] in cambios_post:
                ant, act = cambios_post[p["id"]]
                flecha = " ↑" if (act or 0) > (ant or 0) else " ↓"
            lineas.append(_linea_plaza(p, marca, flecha))
        lineas.append("")
    return lineas

def construir_resumen_completo(plazas_actuales, cambios, total_anterior, advertencias=None):
    total = len(plazas_actuales)
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_actuales)
    diferencia = total - total_anterior

    lineas = ["🚨 <b>¡ACTUALIZACIÓN DE PLAZAS SISTEMA MAESTRO!</b> 🚨", ""]
    if diferencia > 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {total} <b>(+{diferencia})</b> ⬆️")
    elif diferencia < 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {total} <b>({diferencia})</b> ⬇️")
    else:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {total} ↔️")
    lineas.append(f"🆕 <b>Plazas de hoy:</b> {total_hoy}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {total_ayer}")
    lineas.append("")

    vencidas = cambios.get("vencidas", [])
    if cambios["nuevas"] or cambios["eliminadas"] or vencidas or cambios["actualizadas"]:
        lineas.append("--- <b>CAMBIOS</b> ---")
        for p in cambios["nuevas"]:
            lineas.append(f"🆕 {html.escape(p.get('departamento', '?'))} – "
                          f"{html.escape(abreviar_area(p.get('area')))} ({html.escape(str(p.get('municipio', '?')))})")
        for p in cambios["eliminadas"]:
            lineas.append(f"❌ {html.escape(p.get('departamento', '?'))} – "
                          f"{html.escape(abreviar_area(p.get('area')))} ({html.escape(str(p.get('municipio', '?')))})")
        if vencidas:
            lineas.append(f"⌛ {len(vencidas)} plaza(s) cerraron por fecha")
        for a in cambios["actualizadas"][:10]:
            lineas.append(f"🔁 {html.escape(a['departamento'] or '?')} – {html.escape(abreviar_area(a['area']))}: "
                          f"{a['postulados_anterior']} → {a['postulados_actual']}")
        if len(cambios["actualizadas"]) > 10:
            lineas.append(f"… y {len(cambios['actualizadas']) - 10} cambio(s) de postulados más")
        lineas.append("")

    if advertencias:
        for a in advertencias:
            lineas.append(f"⚠️ {html.escape(a)}")
        lineas.append("")

    ids_nuevas = {p["id"] for p in cambios["nuevas"]}
    cambios_post = {a["id"]: (a["postulados_anterior"], a["postulados_actual"]) for a in cambios["actualizadas"]}

    lineas.append("--- <b>TODAS LAS PLAZAS ACTIVAS</b> ---")
    lineas.append("")
    lineas.extend(_bloque_por_departamento(plazas_actuales, ids_nuevas, cambios_post))
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')
    return "\n".join(lineas)

def construir_resumen_filtrado(plazas_filtradas, encabezado=None):
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_filtradas)
    lineas = ["🚨 <b>¡Plazas Sistema Maestro!</b> 🚨", ""]
    if encabezado:
        lineas.append(f"🔎 <b>Filtro:</b> {html.escape(encabezado)}")
    lineas.append(f"🌎 <b>Total plazas activas:</b> {len(plazas_filtradas)}")
    lineas.append(f"🆕 <b>Plazas de hoy:</b> {total_hoy}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {total_ayer}")
    lineas.append("")
    lineas.append("--- <b>TODAS LAS PLAZAS</b> ---")
    lineas.append("")
    if not plazas_filtradas:
        lineas.append("No se encontraron plazas para este filtro.")
    else:
        lineas.extend(_bloque_por_departamento(plazas_filtradas))
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')
    return "\n".join(lineas)

# ============================================================
# TELEGRAM
# ============================================================

def _dividir_mensaje(mensaje, limite):
    lineas = mensaje.split("\n")
    partes, actual = [], ""
    for linea in lineas:
        candidato = f"{actual}\n{linea}" if actual else linea
        if len(candidato) <= limite:
            actual = candidato
            continue
        if actual:
            partes.append(actual)
            actual = ""
        if len(linea) <= limite:
            actual = linea
        else:
            for i in range(0, len(linea), limite):
                partes.append(linea[i:i + limite])
    if actual:
        partes.append(actual)
    return partes if partes else [mensaje[:limite]]

def enviar_telegram(mensaje, chat_id=None):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    destino = chat_id if chat_id is not None else TELEGRAM_CHAT_ID
    partes = _dividir_mensaje(mensaje, 4000)
    for i, parte in enumerate(partes, start=1):
        datos = {"chat_id": destino, "text": parte, "parse_mode": "HTML",
                 "disable_web_page_preview": "true"}
        for intento in range(3):
            try:
                r = requests.post(url, data=datos, timeout=10)
                if r.status_code == 429:
                    espera = 2
                    try:
                        espera = int(r.json().get("parameters", {}).get("retry_after", 2))
                    except Exception:
                        pass
                    time.sleep(min(espera, 30))
                    continue
                if r.status_code != 200:
                    print(f"⚠️ Error Telegram (parte {i}/{len(partes)}): {r.status_code} - {r.text}")
                break
            except Exception as e:
                print(f"⚠️ Error Telegram (parte {i}/{len(partes)}, intento {intento + 1}): {e}")
                time.sleep(1)

def _alerta_error(mensaje):
    """Avisa por Telegram de un error, máximo 1 vez por hora (evita spam cada minuto)."""
    global _ultima_alerta_error_ts
    if time.time() - _ultima_alerta_error_ts < 3600:
        return
    _ultima_alerta_error_ts = time.time()
    enviar_telegram(f"⚠️ <b>Error en el vigilante:</b> {html.escape(mensaje[:300])}")

# ============================================================
# FLUJO PRINCIPAL
# ============================================================

def ejecutar_vigilante(notificar_siempre=False, chat_id=None, forzar_completo=False):
    """
    Debe llamarse a través de ejecutar_con_lock(). Devuelve un texto con el resultado.
    """
    try:
        # 1. Datos actuales (lanza error si el JSON está corrupto)
        plazas_bd = cargar_datos_anteriores()
        total_original = len(plazas_bd)

        estado = cargar_estado_mapa()
        inicializado_previo = bool(estado.get("inicializado", total_original > 0))
        primera_vez = not inicializado_previo

        # 2. Limpiar vencidas
        vigentes, vencidas = limpiar_plazas_vencidas(plazas_bd)
        if vencidas:
            guardar_datos_actuales(vigentes, permitir_vacio=True)
            plazas_bd = vigentes
        plazas_antes = [dict(p) for p in plazas_bd]

        # 3. Chequeo barato del mapa
        conteo_mapa = obtener_conteo_mapa()
        if not conteo_mapa:
            return "El mapa no devolvió marcadores; no se modificó nada."
        total_mapa = sum(conteo_mapa.values())
        conteo_anterior = estado.get("conteo") or {}
        ultima = cargar_ultima_actualizacion_completa()
        segundos = (datetime.now(ZONA_COLOMBIA) - ultima).total_seconds() if ultima else None

        mapa_cambio = dict(conteo_mapa) != conteo_anterior
        toca_completo = (forzar_completo or notificar_siempre or primera_vez or mapa_cambio
                         or ultima is None or segundos >= INTERVALO_SCRAPE_COMPLETO)

        # 4. Scraping completo (con reconciliación segura por departamento)
        ids_nuevas_totales = set()
        deptos_incompletos, deptos_error = [], []
        if toca_completo:
            print("🔄 Scraping completo de todos los departamentos del mapa...")
            for depto in sorted(conteo_mapa):
                try:
                    plazas_depto, completo = obtener_vacantes_por_departamento(depto)
                    plazas_bd, ids_n = reconciliar_departamento(
                        plazas_bd, plazas_depto, depto, completo, conteo_mapa.get(depto))
                    ids_nuevas_totales |= ids_n
                    if not completo:
                        deptos_incompletos.append(depto)
                except Exception as e:
                    deptos_error.append(depto)
                    print(f"⚠️ Error scraping {depto}: {e}")
            guardar_datos_actuales(plazas_bd)

        scrape_ok = toca_completo and not deptos_incompletos and not deptos_error
        if scrape_ok:
            guardar_ultima_actualizacion_completa(datetime.now(ZONA_COLOMBIA))

        nuevo_estado = {
            "total_mapa": total_mapa,
            "inicializado": inicializado_previo or scrape_ok,
            # Solo se "consume" el cambio del mapa si el scrape salió bien; si no, se reintenta.
            "conteo": dict(conteo_mapa) if (scrape_ok or not toca_completo) else conteo_anterior,
        }
        guardar_estado_mapa(nuevo_estado)

        # 5. Detectar cambios
        cambios = detectar_cambios_completos(plazas_bd, plazas_antes)
        cambios["vencidas"] = vencidas
        hay_cambios = bool(cambios["total_nuevas"] or cambios["total_eliminadas"] or vencidas)

        advertencias = []
        if deptos_incompletos:
            advertencias.append("Datos parciales de: " + ", ".join(deptos_incompletos))
        if deptos_error:
            advertencias.append("Falló la lectura de: " + ", ".join(deptos_error))

        # 6. Notificar
        if primera_vez and not notificar_siempre:
            enviar_telegram(f"📥 Base inicializada con {len(plazas_bd)} plazas. "
                            f"Desde ahora solo te aviso los cambios.", chat_id=chat_id)
            return "Base inicializada."

        if hay_cambios or notificar_siempre:
            resumen = construir_resumen_completo(
                plazas_bd, cambios, total_original,
                advertencias=advertencias if notificar_siempre else None)
            enviar_telegram(resumen, chat_id=chat_id)
            return "Notificación enviada."

        if chat_id is not None:
            enviar_telegram("✅ Vigilante ejecutado: no hay cambios nuevos respecto a la última revisión.",
                            chat_id=chat_id)
        return "Sin cambios notificables." if toca_completo else "Sin cambios (mapa igual, no se hizo scrape)."

    except Exception as e:
        traceback.print_exc()
        _alerta_error(str(e))
        return f"Error: {str(e)[:150]}"

def ejecutar_con_lock(**kwargs):
    """
    Ejecuta el vigilante garantizando que solo haya UNA ejecución a la vez.
    Devuelve None si ya había otra en curso.
    """
    if not lock_ejecucion_vigilante.acquire(blocking=False):
        return None
    try:
        with lock_estado_vigilante:
            estado_vigilante_automatico["ultimo_inicio_ts"] = time.time()
        resultado = ejecutar_vigilante(**kwargs)
        with lock_estado_vigilante:
            estado_vigilante_automatico["ultima_ejecucion"] = datetime.now(ZONA_COLOMBIA).isoformat()
            estado_vigilante_automatico["ultimo_resultado"] = resultado
            estado_vigilante_automatico["ejecuciones"] += 1
        return resultado
    finally:
        lock_ejecucion_vigilante.release()

def hilo_vigilante_automatico():
    print(f"🧵 Hilo vigilante iniciado (cada {INTERVALO_VIGILANTE_SEGUNDOS}s).")
    time.sleep(5)
    while True:
        try:
            resultado = ejecutar_con_lock(notificar_siempre=False)
            if resultado is None:
                print("⏳ Vigilante: ya había una ejecución en curso, se omite este ciclo.")
            else:
                print(f"🔍 Chequeo automático: {resultado}")
        except Exception as e:
            print(f"⚠️ Error en hilo vigilante automático: {e}")
        time.sleep(INTERVALO_VIGILANTE_SEGUNDOS)

# ============================================================
# MENÚ INTERACTIVO POR TELEGRAM
# ============================================================

def _cargar_plazas_seguro():
    try:
        return cargar_datos_anteriores()
    except Exception as e:
        print(f"⚠️ No se pudieron cargar las plazas: {e}")
        return []

def obtener_departamentos_en_json():
    deptos = set()
    for p in _cargar_plazas_seguro():
        d = (p.get("departamento") or "").strip()
        if d and d.lower() != "sin departamento":
            deptos.add(d)
    return sorted(deptos)

def obtener_areas_en_json():
    areas = set()
    for p in _cargar_plazas_seguro():
        a = (p.get("area") or "").strip()
        if a and a.lower() != "sin área":
            areas.add(a)
    return sorted(areas)

def filtrar_plazas_por_departamento(nombre):
    return [p for p in _cargar_plazas_seguro() if (p.get("departamento") or "").strip() == nombre]

def filtrar_plazas_por_area(nombre):
    return [p for p in _cargar_plazas_seguro() if (p.get("area") or "").strip() == nombre]

def _texto_sin_mencion(texto):
    return (texto or "").strip().replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()

def _es_comando_menu(texto):
    return bool(texto) and _texto_sin_mencion(texto) in ("menu", "menú", "/menu", "/menú")

def _es_comando_actualizar(texto):
    return bool(texto) and _texto_sin_mencion(texto) in ("actualizar", "/actualizar")

def _enviar_menu_principal(chat_id):
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": "menu_principal"}
    enviar_telegram("📋 <b>Menú principal</b>\n\n1. Departamento\n2. Áreas\n\n"
                    "Responde con el número de la opción.", chat_id=chat_id)

def _enviar_lista(chat_id, tipo, titulo, opciones, vacio):
    if not opciones:
        enviar_telegram(vacio, chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": tipo, "opciones": opciones}
    lineas = [titulo, ""] + [f"{i}. {html.escape(n)}" for i, n in enumerate(opciones, start=1)]
    lineas += ["", "Responde con el número."]
    enviar_telegram("\n".join(lineas), chat_id=chat_id)

def _procesar_seleccion_menu(chat_id, texto):
    with lock_estados_menu:
        estado = estados_menu_chat.get(chat_id)
    if not estado:
        return False
    texto_limpio = (texto or "").strip()
    if not re.fullmatch(r"\d+", texto_limpio):
        return False

    seleccion = int(texto_limpio)
    tipo = estado["tipo"]

    if tipo == "menu_principal":
        if seleccion == 1:
            _enviar_lista(chat_id, "departamento_lista", "📍 <b>Elige un departamento:</b>",
                          obtener_departamentos_en_json(), "No hay departamentos con plazas guardadas todavía.")
        elif seleccion == 2:
            _enviar_lista(chat_id, "area_lista", "📚 <b>Elige un área:</b>",
                          obtener_areas_en_json(), "No hay áreas con plazas guardadas todavía.")
        else:
            enviar_telegram("Opción inválida. Responde 1 o 2.", chat_id=chat_id)
        return True

    if tipo in ("departamento_lista", "area_lista"):
        opciones = estado.get("opciones", [])
        if not (1 <= seleccion <= len(opciones)):
            enviar_telegram(f"Opción inválida. Responde un número entre 1 y {len(opciones)}.", chat_id=chat_id)
            return True
        elegido = opciones[seleccion - 1]
        if tipo == "departamento_lista":
            mensaje = construir_resumen_filtrado(filtrar_plazas_por_departamento(elegido),
                                                 encabezado=f"Departamento: {elegido}")
        else:
            mensaje = construir_resumen_filtrado(filtrar_plazas_por_area(elegido),
                                                 encabezado=f"Área: {elegido}")
        enviar_telegram(mensaje, chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return True

    with lock_estados_menu:
        estados_menu_chat.pop(chat_id, None)
    return False

def _procesar_comando_actualizar(chat_id):
    if lock_ejecucion_vigilante.locked():
        enviar_telegram("⏳ Ya hay una actualización en curso. Intenta de nuevo en un momento.", chat_id=chat_id)
        return
    enviar_telegram("🔎 Actualizando plazas, dame un momento...", chat_id=chat_id)
    resultado = ejecutar_con_lock(notificar_siempre=True, chat_id=chat_id)
    if resultado is None:
        enviar_telegram("⏳ Ya hay una actualización en curso. Intenta de nuevo en un momento.", chat_id=chat_id)
    elif resultado.startswith("Error"):
        enviar_telegram(f"⚠️ {html.escape(resultado)}", chat_id=chat_id)

# ============================================================
# SEGURIDAD
# ============================================================

def _autorizado():
    if not ADMIN_KEY:
        return False
    dada = request.headers.get("X-Admin-Key") or request.args.get("key") or ""
    return hmac.compare_digest(dada, ADMIN_KEY)

def requiere_admin(fn):
    def envoltura(*args, **kwargs):
        if not ADMIN_KEY:
            return {"error": "ADMIN_KEY no está configurada en el servidor; endpoint deshabilitado."}, 503
        if not _autorizado():
            return {"error": "No autorizado (clave incorrecta)."}, 401
        return fn(*args, **kwargs)
    envoltura.__name__ = fn.__name__
    return envoltura

# ============================================================
# ENDPOINTS
# ============================================================

@app.route("/telegram-webhook", methods=["POST"])
def telegram_webhook():
    if TELEGRAM_WEBHOOK_SECRET:
        if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != TELEGRAM_WEBHOOK_SECRET:
            return {"ok": False}, 403
    try:
        update = request.get_json(silent=True) or {}
        mensaje = update.get("message") or update.get("edited_message") or {}
        texto = mensaje.get("text", "")
        chat_id = (mensaje.get("chat") or {}).get("id")

        if chat_id is None:
            return {"ok": True}, 200
        if CHATS_PERMITIDOS is not None and str(chat_id) not in CHATS_PERMITIDOS:
            return {"ok": True}, 200

        if _es_comando_menu(texto):
            _enviar_menu_principal(chat_id)
        elif _procesar_seleccion_menu(chat_id, texto):
            pass
        elif _es_comando_actualizar(texto):
            threading.Thread(target=_procesar_comando_actualizar, args=(chat_id,), daemon=True).start()
    except Exception as e:
        print(f"⚠️ Error en webhook: {e}")
    return {"ok": True}, 200

@app.route("/set-webhook")
@requiere_admin
def set_webhook():
    """Registra este servicio como webhook. Uso: /set-webhook?key=TU_ADMIN_KEY"""
    url_publica = request.host_url.rstrip("/").replace("http://", "https://") + "/telegram-webhook"
    datos = {"url": url_publica, "allowed_updates": json.dumps(["message", "edited_message"])}
    if TELEGRAM_WEBHOOK_SECRET:
        datos["secret_token"] = TELEGRAM_WEBHOOK_SECRET
    try:
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/setWebhook", data=datos, timeout=10)
        return {"webhook_configurado": url_publica, "respuesta_telegram": r.json()}
    except Exception as e:
        return {"error": str(e)}, 500

@app.route("/check")
def check():
    """Disparo manual/externo (inofensivo): respeta lock e intervalo mínimo."""
    with lock_estado_vigilante:
        reciente = time.time() - estado_vigilante_automatico["ultimo_inicio_ts"] < MIN_SEGUNDOS_ENTRE_CHEQUEOS
    if reciente:
        return {"resultado": "Chequeo reciente, se omitió."}, 202
    if lock_ejecucion_vigilante.locked():
        return {"resultado": "Ya hay una ejecución en curso, se omitió este chequeo."}, 409

    def tarea():
        try:
            ejecutar_con_lock(notificar_siempre=False)
        except Exception as e:
            print(f"Error en hilo de /check: {e}")
    threading.Thread(target=tarea, daemon=True).start()
    return {"resultado": "Tarea iniciada en segundo plano"}, 202

@app.route("/check-force")
@requiere_admin
def check_force():
    if lock_ejecucion_vigilante.locked():
        return {"resultado": "Ya hay una ejecución en curso."}, 409

    def tarea():
        try:
            ejecutar_con_lock(notificar_siempre=True)
        except Exception as e:
            print(f"Error en hilo de /check-force: {e}")
    threading.Thread(target=tarea, daemon=True).start()
    return {"resultado": "Tarea (con notificación) iniciada en segundo plano"}, 202

@app.route("/status")
def status():
    with lock_estado_vigilante:
        return {
            "intervalo_segundos": INTERVALO_VIGILANTE_SEGUNDOS,
            "intervalo_scrape_completo": INTERVALO_SCRAPE_COMPLETO,
            "ultima_ejecucion": estado_vigilante_automatico["ultima_ejecucion"],
            "ultimo_resultado": estado_vigilante_automatico["ultimo_resultado"],
            "ejecuciones_desde_arranque": estado_vigilante_automatico["ejecuciones"],
            "scrape_en_curso": lock_ejecucion_vigilante.locked(),
        }

@app.route("/verjson")
def verjson():
    try:
        return {"ruta": os.path.abspath(ARCHIVO_DATOS), "contenido": cargar_datos_anteriores()}
    except Exception as e:
        return {"ruta": os.path.abspath(ARCHIVO_DATOS), "contenido": f"Error: {e}"}

@app.route("/departamentos")
def obtener_departamentos():
    try:
        conteo = obtener_conteo_mapa()
        if not conteo:
            return {"error": "No se encontraron departamentos"}, 404
        contador_json = Counter(norm(p.get("departamento")) for p in _cargar_plazas_seguro())
        departamentos = [{"nombre": n, "cantidad": c, "en_json": contador_json.get(norm(n), 0)}
                         for n, c in conteo.items()]
        departamentos.sort(key=lambda x: x["cantidad"], reverse=True)
        return {"departamentos": departamentos, "total": sum(conteo.values()),
                "departamentos_unicos": len(departamentos)}
    except requests.exceptions.RequestException as e:
        return {"error": f"Error de conexión: {str(e)}"}, 500
    except Exception as e:
        return {"error": f"Error inesperado: {str(e)}"}, 500

@app.route("/agregar-departamento", methods=["POST"])
@requiere_admin
def agregar_departamento():
    data = request.get_json(silent=True) or {}
    nombre = (data.get("departamento") or "").strip()
    if not nombre:
        return {"error": "Se requiere el nombre del departamento"}, 400

    if not lock_ejecucion_vigilante.acquire(blocking=False):
        return {"error": "Hay un scrape en curso; intenta de nuevo en un momento."}, 409
    try:
        try:
            plazas_dep, completo = obtener_vacantes_por_departamento(nombre)
        except ValueError as e:
            return {"error": str(e)}, 400
        if not plazas_dep:
            return {"error": f"No se encontraron plazas para '{nombre}'."}, 404

        try:
            esperada = obtener_conteo_mapa().get(nombre)
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            esperada = None

        plazas_bd = cargar_datos_anteriores()
        fusionadas, ids_nuevas = reconciliar_departamento(plazas_bd, plazas_dep, nombre, completo, esperada)
        guardar_datos_actuales(fusionadas)

        return {
            "mensaje": f"✅ Se procesaron {len(plazas_dep)} plazas de '{nombre}'"
                       + ("" if completo else " (lectura parcial, no se borró nada)"),
            "plazas_encontradas": len(plazas_dep),
            "total_plazas_en_json": len(fusionadas),
            "plazas_nuevas": len(ids_nuevas),
        }
    except Exception as e:
        return {"error": f"Error al agregar departamento: {str(e)}"}, 500
    finally:
        lock_ejecucion_vigilante.release()

@app.route("/limpiar-vencidas", methods=["POST"])
@requiere_admin
def limpiar_vencidas():
    try:
        plazas = cargar_datos_anteriores()
        if not plazas:
            return {"mensaje": "No hay plazas en el JSON", "eliminadas": 0, "restantes": 0}, 200
        vigentes, vencidas = limpiar_plazas_vencidas(plazas)
        if vencidas:
            guardar_datos_actuales(vigentes, permitir_vacio=True)
            return {"mensaje": f"Se eliminaron {len(vencidas)} plazas vencidas.",
                    "eliminadas": len(vencidas), "restantes": len(vigentes)}, 200
        return {"mensaje": "No hay plazas vencidas.", "eliminadas": 0, "restantes": len(plazas)}, 200
    except Exception as e:
        return {"error": str(e)}, 500

@app.route("/limpiar-json", methods=["POST"])
@requiere_admin
def limpiar_json():
    """Reinicia la base. La siguiente ejecución la reconstruye SIN notificar cada plaza como nueva."""
    try:
        eliminados = []
        for ruta in (ARCHIVO_DATOS, ARCHIVO_ESTADO, ARCHIVO_ULTIMA_ACTUALIZACION):
            if os.path.exists(ruta):
                os.remove(ruta)
                eliminados.append(os.path.basename(ruta))
        return {"mensaje": "Eliminados: " + (", ".join(eliminados) if eliminados else "nada que eliminar")}, 200
    except Exception as e:
        return {"error": f"Error al limpiar JSON: {str(e)}"}, 500

@app.route("/cargar-json", methods=["POST"])
@requiere_admin
def cargar_json():
    try:
        data = json.loads(request.get_data(as_text=True) or "")
    except json.JSONDecodeError as e:
        return {"error": f"El JSON es inválido: {str(e)}"}, 400
    if not isinstance(data, list) or not data:
        return {"error": "El JSON debe ser una lista de objetos, no vacía"}, 400
    for i, p in enumerate(data):
        if not isinstance(p, dict) or not all(k in p for k in ("id", "departamento", "area")):
            return {"error": f"El elemento {i} no tiene los campos mínimos (id, departamento, area)"}, 400

    guardar_datos_actuales(data)
    try:
        estado = cargar_estado_mapa()
        estado["inicializado"] = True
        estado["total_mapa"] = obtener_total_plazas_mapa()
        guardar_estado_mapa(estado)
    except Exception as e:
        print(f"Error al actualizar estado del mapa: {e}")
    return {"mensaje": f"✅ JSON guardado correctamente ({len(data)} plazas)"}

@app.route("/")
def home():
    try:
        contenido = json.dumps(cargar_datos_anteriores(), indent=2, ensure_ascii=False)
    except Exception as e:
        contenido = f"Error: {e}"

    pagina = """<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Vigilante de Vacantes</title>
<style>
 body { font-family: Arial, sans-serif; margin: 30px; }
 button { padding: 10px 20px; margin: 5px; cursor: pointer; }
 input[type=password] { padding: 8px; }
 pre { background: #f4f4f4; padding: 15px; border-radius: 5px; overflow: auto; max-height: 400px; }
 textarea { width: 100%; padding: 10px; font-family: monospace; box-sizing: border-box; }
 .card { border: 1px solid #ddd; padding: 20px; margin-bottom: 20px; border-radius: 8px; }
 .btn-primary { background: #007bff; color: white; border: none; }
 .btn-success { background: #28a745; color: white; border: none; }
 .btn-warning { background: #ffc107; color: black; border: none; }
 .btn-info { background: #17a2b8; color: white; border: none; }
 .btn-danger { background: #dc3545; color: white; border: none; }
 .btn-departamento { padding: 5px 10px; font-size: 12px; margin: 2px; border: none; }
 table { width: 100%; border-collapse: collapse; margin-top: 10px; }
 th, td { padding: 8px; border: 1px solid #ddd; text-align: left; }
 th { background: #f2f2f2; }
</style>
</head>
<body>
<h1>🕵️ Vigilante de Vacantes</h1>

<div class="card">
 <h2>Clave de administrador</h2>
 <input type="password" id="adminKey" placeholder="ADMIN_KEY">
 <button class="btn-info" onclick="guardarClave()">Guardar en esta pestaña</button>
 <div style="font-size:12px;color:#666">Necesaria para forzar, limpiar, cargar o agregar departamentos.</div>
</div>

<div class="card">
 <h2>Acciones</h2>
 <button class="btn-primary" onclick="ejecutarCheck()">🚀 Ejecutar vigilante (solo si hay cambios)</button>
 <button class="btn-success" onclick="ejecutarCheckForce()">📢 Ejecutar vigilante (SIEMPRE notificar)</button>
 <button class="btn-danger" onclick="limpiarJSON()">🗑️ Limpiar JSON (reiniciar base)</button>
 <button class="btn-info" onclick="verDepartamentos()">📍 Ver departamentos con plazas</button>
 <button class="btn-primary" id="btnTodos" onclick="agregarTodos()">🚀 Agregar todos los departamentos pendientes</button>
 <button class="btn-danger" onclick="limpiarVencidas()">🗑️ Eliminar plazas vencidas</button>
 <div id="resultado" style="margin-top:10px;color:green;"></div>
</div>

<div class="card" id="departamentos-card" style="display:none;">
 <h2>📍 Departamentos con Plazas</h2>
 <div id="departamentos-content"></div>
</div>

<div class="card">
 <h2>Contenido del JSON (base de datos)</h2>
 <pre id="jsonView">__CONTENIDO_JSON__</pre>
</div>

<div class="card">
 <h2>Cargar JSON manualmente (reemplaza toda la base)</h2>
 <form id="cargaForm">
  <textarea rows="10" placeholder="Pega aquí el JSON (lista de objetos)"></textarea><br>
  <button type="submit">📤 Cargar JSON</button>
 </form>
</div>

<script>
const $ = id => document.getElementById(id);
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function clave() { return sessionStorage.getItem('adminKey') || ''; }
function guardarClave() {
  sessionStorage.setItem('adminKey', $('adminKey').value.trim());
  $('resultado').textContent = '🔑 Clave guardada en esta pestaña.';
}
async function api(url, opts) {
  opts = opts || {};
  opts.headers = Object.assign({'X-Admin-Key': clave()}, opts.headers || {});
  const r = await fetch(url, opts);
  let data = {};
  try { data = await r.json(); } catch (e) {}
  if (!r.ok && !data.error) data.error = 'HTTP ' + r.status + (data.resultado ? ': ' + data.resultado : '');
  return data;
}
function msg(t) { $('resultado').textContent = t; }

async function ejecutarCheck() {
  const d = await api('/check');
  msg(d.error ? '❌ ' + d.error : '✅ ' + d.resultado);
}
async function ejecutarCheckForce() {
  msg('⏳ Iniciando...');
  const d = await api('/check-force');
  msg(d.error ? '❌ ' + d.error : '✅ ' + d.resultado);
}
async function verDepartamentos() {
  const card = $('departamentos-card'), content = $('departamentos-content');
  card.style.display = 'block';
  content.textContent = '⏳ Cargando departamentos...';
  const data = await api('/departamentos');
  if (data.error) { content.textContent = '❌ ' + data.error; return; }
  let h = `<p><b>Total plazas (mapa):</b> ${data.total}</p><p><b>Departamentos únicos:</b> ${data.departamentos_unicos}</p>
    <table><thead><tr><th>Departamento</th><th style="text-align:center">Cantidad</th><th style="text-align:center">Acción</th></tr></thead><tbody>`;
  data.departamentos.forEach((d, i) => {
    const completo = d.en_json >= d.cantidad;
    h += `<tr style="background:${i % 2 ? '#f9f9f9' : '#fff'}"><td><b>${esc(d.nombre)}</b></td>
      <td style="text-align:center"><b>${d.cantidad}</b> (JSON: ${d.en_json})</td>
      <td style="text-align:center"><button class="btn-departamento ${completo ? 'btn-success' : 'btn-warning'}"
        data-nombre="${esc(d.nombre)}" ${completo ? 'disabled' : ''}>${completo ? '✅ Completo' : '📥 Agregar ' + d.cantidad + ' plazas'}</button></td></tr>`;
  });
  h += `</tbody></table><br><button onclick="$('departamentos-card').style.display='none'">Cerrar</button>`;
  content.innerHTML = h;
}
$('departamentos-content').addEventListener('click', e => {
  const b = e.target.closest('button[data-nombre]');
  if (b && !b.disabled) agregarDepartamento(b.dataset.nombre);
});
async function actualizarContenidoJSON() {
  try {
    const r = await fetch('/verjson', {cache: 'no-store'});
    const d = await r.json();
    $('jsonView').textContent = typeof d.contenido === 'string' ? d.contenido : JSON.stringify(d.contenido, null, 2);
  } catch (e) { console.error('Error al actualizar JSON:', e); }
}
setInterval(actualizarContenidoJSON, 30000);

async function agregarDepartamento(nombre) {
  if (!confirm(`¿Agregar todas las plazas de "${nombre}" al JSON?`)) return;
  msg(`⏳ Agregando plazas de ${nombre}...`);
  const d = await api('/agregar-departamento', {method: 'POST',
    headers: {'Content-Type': 'application/json'}, body: JSON.stringify({departamento: nombre})});
  if (d.error) { msg('❌ ' + d.error); alert('❌ ' + d.error); return; }
  msg(`✅ ${d.mensaje} (Total en JSON: ${d.total_plazas_en_json})`);
  verDepartamentos(); actualizarContenidoJSON();
}
async function limpiarJSON() {
  if (!confirm('⚠️ ¿ELIMINAR TODOS los datos guardados? No se puede deshacer.')) return;
  const d = await api('/limpiar-json', {method: 'POST'});
  if (d.error) { msg('❌ ' + d.error); return; }
  msg('✅ ' + d.mensaje); location.reload();
}
async function agregarTodos() {
  if (!confirm('⚠️ ¿Agregar las plazas de TODOS los departamentos pendientes?')) return;
  const btn = $('btnTodos'); btn.disabled = true;
  try {
    msg('⏳ Obteniendo lista de departamentos...');
    const data = await api('/departamentos');
    if (data.error) { msg('❌ ' + data.error); return; }
    const pend = data.departamentos.filter(d => d.en_json < d.cantidad);
    if (!pend.length) { msg('✅ Todos los departamentos ya están completos.'); return; }
    let ok = 0; const errores = [];
    for (let i = 0; i < pend.length; i++) {
      msg(`⏳ Agregando ${pend[i].nombre}... (${i + 1}/${pend.length})`);
      const d = await api('/agregar-departamento', {method: 'POST',
        headers: {'Content-Type': 'application/json'}, body: JSON.stringify({departamento: pend[i].nombre})});
      if (d.error) errores.push(`${pend[i].nombre}: ${d.error}`); else ok++;
    }
    msg(`✅ Proceso completado: ${ok} departamento(s) agregados.` + (errores.length ? ` Errores: ${errores.join(' | ')}` : ''));
    verDepartamentos(); actualizarContenidoJSON();
  } finally { btn.disabled = false; }
}
async function limpiarVencidas() {
  if (!confirm('⚠️ ¿Eliminar todas las plazas cuya fecha de cierre ya pasó?')) return;
  const d = await api('/limpiar-vencidas', {method: 'POST'});
  if (d.error) { msg('❌ ' + d.error); return; }
  msg(`✅ ${d.mensaje} (Restantes: ${d.restantes || 0})`);
  actualizarContenidoJSON();
}
$('cargaForm').addEventListener('submit', async function (e) {
  e.preventDefault();
  const txt = this.querySelector('textarea').value.trim();
  if (!txt) { alert('❌ Pega un JSON.'); return; }
  try { JSON.parse(txt); } catch (err) { alert('❌ JSON inválido: ' + err.message); return; }
  const d = await api('/cargar-json', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: txt});
  alert(d.error ? '❌ ' + d.error : '✅ ' + d.mensaje);
  if (!d.error) location.reload();
});
$('adminKey').value = clave();
</script>
</body>
</html>"""
    return pagina.replace("__CONTENIDO_JSON__", html.escape(contenido))

# ============================================================
# ARRANQUE DE HILOS
# ============================================================
# Con Gunicorn usa UN worker:  gunicorn app:app --workers 1 --threads 4 --timeout 120
# Aun así, este candado de archivo evita que dos procesos arranquen el vigilante a la vez.
_archivo_lock_proceso = None

def _es_proceso_lider():
    global _archivo_lock_proceso
    try:
        import fcntl
    except ImportError:      # Windows / desarrollo local
        return True
    try:
        _archivo_lock_proceso = open(ARCHIVO_LOCK_PROCESO, "w")
        fcntl.flock(_archivo_lock_proceso, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return True
    except OSError:
        return False

if os.environ.get("DISABLE_BACKGROUND") != "1" and _es_proceso_lider():
    threading.Thread(target=hilo_vigilante_automatico, daemon=True).start()
else:
    print("ℹ️ Este proceso no ejecuta el hilo vigilante (otro proceso ya lo tiene o está deshabilitado).")

# ============================================================
# CONFIGURACIÓN (resumen)
# ============================================================
# Variables de entorno:
#   TELEGRAM_TOKEN, TELEGRAM_CHAT_ID          (obligatorias)
#   ADMIN_KEY                                  (para endpoints que modifican datos)
#   TELEGRAM_WEBHOOK_SECRET                    (opcional, recomendado)
#   ALLOWED_CHAT_IDS                           (opcional, ids separados por coma)
#   DATA_DIR=/data                             (si montas un Persistent Disk en Render)
#   INTERVALO_VIGILANTE_SEGUNDOS=60            (chequeo barato del mapa)
#   INTERVALO_SCRAPE_COMPLETO=300              (scrape completo aunque el mapa no cambie)
#
# Webhook: visita  https://<TU_APP>.onrender.com/set-webhook?key=<ADMIN_KEY>  una vez.
# cron-job.org: apúntalo a  https://<TU_APP>.onrender.com/status  (solo para mantener despierto
# el servicio en el plan gratuito; el trabajo real lo hace el hilo interno).

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
