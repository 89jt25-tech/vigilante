from flask import Flask, request
import requests
import os
import re
import json
import html
import sqlite3
import threading
from contextlib import contextmanager
from functools import wraps
from datetime import datetime, timedelta
from collections import defaultdict, Counter
from bs4 import BeautifulSoup
import xml.etree.ElementTree as ET
from zoneinfo import ZoneInfo
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 10 * 1024 * 1024  # 10 MB

# ============================================================
# CONFIGURACIÓN
# ============================================================
TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")

URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ZONA_COLOMBIA = ZoneInfo("America/Bogota")

# Con un Render Disk montado en /data la base sobrevive a los deploys.
# También puedes fijar la ruta con la variable DB_PATH.
DB_PATH = os.environ.get("DB_PATH") or ("/data/plazas.db" if os.path.isdir("/data") else "plazas.db")
ARCHIVO_JSON_ANTIGUO = "plazas.json"  # solo para migración automática

MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6
MINUTOS_MAX_ERROR_TELEGRAM = 30
MINUTOS_VIGENCIA_MENU = 10

HEADERS_AJAX = {
    "accept": "application/xml, text/xml, */*; q=0.01",
    "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
    "faces-request": "partial/ajax",
    "x-requested-with": "XMLHttpRequest",
    "User-Agent": "Mozilla/5.0",
}

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


def _norm(texto):
    return (texto or "").strip().lower()


# ============================================================
# BASE DE DATOS (SQLite)
# ============================================================
lock_db = threading.RLock()
lock_ejecucion_vigilante = threading.Lock()


@contextmanager
def db():
    """Conexión SQLite con lock global, commit automático y cierre garantizado."""
    with lock_db:
        conn = sqlite3.connect(DB_PATH, timeout=30)
        try:
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()


def init_db():
    carpeta = os.path.dirname(os.path.abspath(DB_PATH))
    os.makedirs(carpeta, exist_ok=True)
    with db() as c:
        c.execute("PRAGMA journal_mode=WAL")
        c.execute("""CREATE TABLE IF NOT EXISTS plazas (
            id TEXT PRIMARY KEY,
            departamento TEXT,
            area TEXT,
            cierre TEXT,
            data TEXT NOT NULL
        )""")
        c.execute("CREATE TABLE IF NOT EXISTS meta (clave TEXT PRIMARY KEY, valor TEXT)")
        c.execute("""CREATE TABLE IF NOT EXISTS menu_estado (
            chat_id TEXT PRIMARY KEY,
            tipo TEXT NOT NULL,
            opciones TEXT,
            actualizado TEXT NOT NULL
        )""")


def cargar_datos_anteriores():
    with db() as c:
        filas = c.execute("SELECT data FROM plazas ORDER BY rowid").fetchall()
    return [json.loads(f[0]) for f in filas]


def guardar_datos_actuales(plazas):
    """Reemplaza todas las plazas en una sola transacción (atómico)."""
    with db() as c:
        c.execute("DELETE FROM plazas")
        c.executemany(
            "INSERT OR REPLACE INTO plazas (id, departamento, area, cierre, data) VALUES (?,?,?,?,?)",
            [(p["id"], p.get("departamento"), p.get("area"), p.get("cierre"),
              json.dumps(p, ensure_ascii=False)) for p in plazas],
        )


def get_meta(clave, defecto=None):
    with db() as c:
        fila = c.execute("SELECT valor FROM meta WHERE clave=?", (clave,)).fetchone()
    if not fila:
        return defecto
    try:
        return json.loads(fila[0])
    except Exception:
        return defecto


def set_meta(clave, valor):
    with db() as c:
        c.execute("INSERT OR REPLACE INTO meta (clave, valor) VALUES (?,?)",
                  (clave, json.dumps(valor, ensure_ascii=False)))


def set_estado_menu(chat_id, tipo, opciones=None):
    with db() as c:
        c.execute(
            "INSERT OR REPLACE INTO menu_estado (chat_id, tipo, opciones, actualizado) VALUES (?,?,?,?)",
            (str(chat_id), tipo, json.dumps(opciones or [], ensure_ascii=False),
             datetime.now(ZONA_COLOMBIA).isoformat()),
        )


def get_estado_menu(chat_id, solo_vigente=False):
    with db() as c:
        fila = c.execute("SELECT tipo, opciones, actualizado FROM menu_estado WHERE chat_id=?",
                         (str(chat_id),)).fetchone()
    if not fila:
        return None
    if solo_vigente:
        try:
            edad = datetime.now(ZONA_COLOMBIA) - datetime.fromisoformat(fila[2])
            if edad > timedelta(minutes=MINUTOS_VIGENCIA_MENU):
                return None
        except Exception:
            return None
    return {"tipo": fila[0], "opciones": json.loads(fila[1] or "[]")}


def migrar_json_antiguo():
    """Si existe un plazas.json viejo y la base está vacía, lo importa una vez."""
    try:
        if not os.path.exists(ARCHIVO_JSON_ANTIGUO) or cargar_datos_anteriores():
            return
        with open(ARCHIVO_JSON_ANTIGUO, "r", encoding="utf-8") as f:
            datos = json.load(f)
        if not isinstance(datos, list) or not datos:
            return
        for p in datos:
            p["id"] = generar_id(p)
        guardar_datos_actuales(desambiguar_ids(datos))
        print(f"📦 Migradas {len(datos)} plazas desde {ARCHIVO_JSON_ANTIGUO} a SQLite.")
    except Exception as e:
        print(f"⚠️ No se pudo migrar el JSON antiguo: {e}")


# ============================================================
# HTTP / SCRAPING
# ============================================================

def nueva_sesion():
    s = requests.Session()
    retry = Retry(total=3, backoff_factor=1.5, status_forcelist=[429, 500, 502, 503, 504],
                  allowed_methods=None)
    s.mount("https://", HTTPAdapter(max_retries=retry))
    s.headers.update({"User-Agent": "Mozilla/5.0"})
    return s


PATRON_MARCADOR = re.compile(r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'")


def obtener_info_mapa(session=None):
    """Una sola petición al mapa: total de marcadores y conteo por departamento."""
    s = session or nueva_sesion()
    r = s.get(URL_PAGINA, timeout=30)
    r.raise_for_status()
    titulos = PATRON_MARCADOR.findall(r.text)
    conteo = Counter(t.split(" - ")[0].strip() for t in titulos)
    return {
        "total": len(titulos),
        "conteo": conteo,
        "conteo_norm": {_norm(k): v for k, v in conteo.items()},
    }


def obtener_viewstate(session):
    r = session.get(URL_PAGINA, timeout=30)
    m = re.search(r'javax\.faces\.ViewState" value="([^"]+)"', r.text)
    return m.group(1) if m else None


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
        return etiqueta.get_text(strip=True).replace(patron, "").strip()
    return None


def _valor_estable(x):
    """Ignora valores de relleno ('Sin ...') para que el ID no cambie si un dato falta."""
    if not x or str(x).startswith("Sin "):
        return ""
    return str(x)


def generar_id(p):
    """ID solo con campos estables (sin zona ni tipo de zona, que dependen del detalle)."""
    partes = [p.get("departamento"), p.get("area"), p.get("municipio"), p.get("cierre"),
              p.get("secretaria"), p.get("cargo"), p.get("tipo_priorizacion")]
    return "|".join(_valor_estable(x) for x in partes).lower().replace(" ", "_")


def parsear_vacantes(html_fragmento):
    soup = BeautifulSoup(html_fragmento, "html.parser")
    vacantes = []
    for panel in soup.select("div.vacante"):
        cargo = extraer_campo(panel, r"Cargo")
        postulados_texto = extraer_campo(panel, r"Postulados:")
        m = re.search(r"\d+", postulados_texto) if postulados_texto else None
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

        vacante = {
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
        }
        vacante["id"] = generar_id(vacante)
        vacantes.append(vacante)
    return vacantes


def expandir_todos_detalles(session, viewstate, html_actual):
    """Hace clic en todos los 'Ver detalle' y devuelve el HTML expandido."""
    soup = BeautifulSoup(html_actual, "html.parser")
    for _ in range(50):
        enlaces = soup.select("div.vacante a.ui-commandlink")
        enlaces_ver = [a for a in enlaces if a.get_text(strip=True) == "Ver detalle"]
        if not enlaces_ver:
            break
        source_id = enlaces_ver[0].get("id")
        if not source_id:
            break

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
        resultado = extraer_actualizaciones(response.text)
        if resultado.get("viewstate"):
            viewstate = resultado["viewstate"]
        if resultado.get("html"):
            html_actual = resultado["html"]
        else:
            break
        soup = BeautifulSoup(html_actual, "html.parser")

    return html_actual, viewstate


def desambiguar_ids(vacantes):
    conteo_total = Counter(v["id"] for v in vacantes)
    visto = defaultdict(int)
    for v in vacantes:
        base = v["id"]
        if conteo_total[base] > 1:
            visto[base] += 1
            v["id"] = f"{base}__{visto[base]}"
    return vacantes


def _datos_filtro(viewstate, codigo_departamento, filas):
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
        "form-busqueda:tabla-vacantes_rppDD": str(filas),
    }


def cambiar_filtro_departamento(session, viewstate, codigo_departamento):
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:idInputDepartamento",
        "javax.faces.partial.execute": "@all",
        "javax.faces.partial.render": "accordion",
        "javax.faces.behavior.event": "change",
        "javax.faces.partial.event": "change",
    }
    data.update(_datos_filtro(viewstate, codigo_departamento, FILAS_POR_PAGINA))
    r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
    resultado = extraer_actualizaciones(r.text)
    return resultado["html"], resultado["viewstate"] or viewstate


def pedir_pagina_filtrada(session, viewstate, first, rows, codigo_departamento):
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:tabla-vacantes",
        "javax.faces.partial.execute": "form-busqueda:tabla-vacantes",
        "javax.faces.partial.render": "form-busqueda:tabla-vacantes",
        "form-busqueda:tabla-vacantes": "form-busqueda:tabla-vacantes",
        "form-busqueda:tabla-vacantes_pagination": "true",
        "form-busqueda:tabla-vacantes_first": str(first),
        "form-busqueda:tabla-vacantes_rows": str(rows),
    }
    data.update(_datos_filtro(viewstate, codigo_departamento, rows))
    r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
    resultado = extraer_actualizaciones(r.text)
    nuevo_viewstate = resultado["viewstate"] or viewstate
    html_frag = resultado["html"]
    try:
        return expandir_todos_detalles(session, nuevo_viewstate, html_frag)
    except Exception as e:
        print(f"⚠️ Error al expandir detalles en página {first // rows + 1}: {e}")
        return html_frag, nuevo_viewstate


def obtener_vacantes_por_departamento(nombre_departamento):
    nombre_clean = _norm(nombre_departamento)
    codigo = DEPARTAMENTOS_CODIGOS.get(nombre_clean)
    if not codigo:
        for key, value in DEPARTAMENTOS_CODIGOS.items():
            if nombre_clean in key or key in nombre_clean:
                codigo = value
                break
    if not codigo:
        raise ValueError(f"Departamento '{nombre_departamento}' no encontrado en el mapeo")

    session = nueva_sesion()
    viewstate = obtener_viewstate(session)
    if not viewstate:
        raise RuntimeError("No se pudo obtener el ViewState inicial")

    _, viewstate = cambiar_filtro_departamento(session, viewstate, codigo)

    todas = []
    first = 0
    for _ in range(MAX_PAGINAS):
        html_frag, viewstate = pedir_pagina_filtrada(session, viewstate, first, FILAS_POR_PAGINA, codigo)
        vacantes = parsear_vacantes(html_frag)

        # Si la expansión de detalles falló (zona sin datos), reintenta la página una vez
        if vacantes and any(v["zona"] == "Sin zona" for v in vacantes):
            html_frag, viewstate = pedir_pagina_filtrada(session, viewstate, first, FILAS_POR_PAGINA, codigo)
            reintento = parsear_vacantes(html_frag)
            if reintento:
                vacantes = reintento

        if not vacantes:
            break
        todas.extend(vacantes)
        first += FILAS_POR_PAGINA
        if len(vacantes) < FILAS_POR_PAGINA:
            break

    return desambiguar_ids(todas)


# ============================================================
# FUSIÓN Y LIMPIEZA
# ============================================================

def _actualizar_sin_degradar(existente, nuevo):
    """Actualiza sin pisar un dato bueno con un relleno 'Sin ...'."""
    for k, v in nuevo.items():
        anterior = existente.get(k)
        if (isinstance(v, str) and v.startswith("Sin ")
                and isinstance(anterior, str) and anterior and not anterior.startswith("Sin ")):
            continue
        existente[k] = v


def fusionar_plazas_reconciliando_seguro(plazas_bd, scrapeadas, departamento, cantidad_esperada=None):
    """
    Agrega/actualiza las plazas del departamento y elimina las que desaparecieron,
    SOLO si el scrape parece completo (no vacío y con al menos las plazas que
    indica el mapa). Si no, hace un merge aditivo (nunca borra).
    """
    ndep = _norm(departamento)
    plazas_bd = [dict(p) for p in plazas_bd]
    ids_scrapeadas = {p["id"] for p in scrapeadas}
    completo = bool(scrapeadas) and not (
        cantidad_esperada is not None and len(scrapeadas) < cantidad_esperada
    )
    if not completo:
        print(f"⚠️ Scrape de {departamento} no confiable "
              f"({len(scrapeadas)} de {cantidad_esperada}); solo se agrega/actualiza.")

    resultado = []
    por_id = {}
    for p in plazas_bd:
        del_depto = _norm(p.get("departamento")) == ndep
        if del_depto and completo and p["id"] not in ids_scrapeadas:
            continue
        resultado.append(p)
        por_id[p["id"]] = p

    ids_nuevas = set()
    for p in scrapeadas:
        if p["id"] in por_id:
            _actualizar_sin_degradar(por_id[p["id"]], p)
        else:
            nuevo = dict(p)
            resultado.append(nuevo)
            por_id[nuevo["id"]] = nuevo
            ids_nuevas.add(nuevo["id"])
    return resultado, ids_nuevas


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
        fecha = parsear_fecha_cierre(p.get("cierre"))
        if fecha and fecha <= ahora:
            vencidas.append(p)
        else:
            vigentes.append(p)
    return vigentes, vencidas


def detectar_cambios_completos(plazas_actuales, plazas_anteriores):
    ant = {p["id"]: p for p in plazas_anteriores}
    act = {p["id"]: p for p in plazas_actuales}
    nuevas = [p for i, p in act.items() if i not in ant]
    eliminadas = [p for i, p in ant.items() if i not in act]
    actualizadas = [
        {"id": i, "departamento": p["departamento"], "area": p["area"],
         "postulados_anterior": ant[i]["postulados"], "postulados_actual": p["postulados"]}
        for i, p in act.items() if i in ant and p["postulados"] != ant[i]["postulados"]
    ]
    return {
        "nuevas": nuevas, "eliminadas": eliminadas, "actualizadas": actualizadas,
        "total_nuevas": len(nuevas), "total_eliminadas": len(eliminadas),
        "total_actualizadas": len(actualizadas),
    }


def contar_plazas_por_activacion(plazas):
    """Cuenta plazas activadas hoy y ayer (activación = cierre - 24h)."""
    hoy = datetime.now(ZONA_COLOMBIA).date()
    ayer = hoy - timedelta(days=1)
    c_hoy = c_ayer = 0
    for p in plazas:
        fecha = parsear_fecha_cierre(p.get("cierre"))
        if fecha:
            d = (fecha - timedelta(days=1)).date()
            if d == hoy:
                c_hoy += 1
            elif d == ayer:
                c_ayer += 1
    return c_hoy, c_ayer


# ============================================================
# MENSAJES DE TELEGRAM
# ============================================================

def _api_telegram(metodo, datos):
    try:
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/{metodo}", data=datos, timeout=10)
        if r.status_code != 200:
            print(f"⚠️ Telegram {metodo}: {r.status_code} - {r.text}")
        return r
    except Exception as e:
        print(f"⚠️ Telegram {metodo}: {e}")
        return None


def _dividir_mensaje(mensaje, limite):
    partes, actual = [], ""
    for linea in mensaje.split("\n"):
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


def enviar_telegram(mensaje, chat_id=None, reply_markup=None):
    destino = chat_id if chat_id is not None else TELEGRAM_CHAT_ID
    partes = _dividir_mensaje(mensaje, 4000)
    for i, parte in enumerate(partes, start=1):
        datos = {"chat_id": destino, "text": parte, "parse_mode": "HTML",
                 "disable_web_page_preview": "true"}
        if reply_markup and i == len(partes):
            datos["reply_markup"] = json.dumps(reply_markup)
        _api_telegram("sendMessage", datos)


def enviar_error_limitado(texto):
    """Avisa errores al chat principal, máximo uno cada 30 minutos."""
    try:
        ultimo = get_meta("ultimo_error_notificado")
        if ultimo:
            edad = datetime.now(ZONA_COLOMBIA) - datetime.fromisoformat(ultimo)
            if edad < timedelta(minutes=MINUTOS_MAX_ERROR_TELEGRAM):
                return
        set_meta("ultimo_error_notificado", datetime.now(ZONA_COLOMBIA).isoformat())
        enviar_telegram(f"⚠️ <b>Error en vigilante:</b> {html.escape(texto[:300])}")
    except Exception as e:
        print(f"⚠️ No se pudo notificar error: {e}")


def _lineas_plazas(plazas, ids_nuevas=None, con_zona=True):
    ids_nuevas = ids_nuevas or set()
    deptos = defaultdict(list)
    for p in plazas:
        deptos[p["departamento"]].append(p)
    lineas = []
    for depto in sorted(deptos.keys()):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            area = html.escape(abreviar_area(p["area"]))
            mun = html.escape(p["municipio"])
            zona = html.escape(p["zona_tipo"])
            marca = " 🆕" if p["id"] in ids_nuevas else ""
            lineas.append(f"  • {area} ({mun} - {zona}){marca} – {p['postulados']} postulados")
        lineas.append("")
    return lineas


def _resumen_corto(p):
    return f"  • {html.escape(abreviar_area(p['area']))} ({html.escape(p['municipio'])}, {html.escape(p['departamento'])})"


def construir_resumen_completo(plazas_actuales, plazas_anteriores, total_mapa, cambios, vencidas):
    hoy, ayer = contar_plazas_por_activacion(plazas_actuales)
    total = len(plazas_actuales)
    diferencia = total - len(plazas_anteriores)
    ids_nuevas = {p["id"] for p in cambios["nuevas"]}

    flecha = f"<b>(+{diferencia})</b> ⬆️" if diferencia > 0 else (f"<b>({diferencia})</b> ⬇️" if diferencia < 0 else "↔️")

    lineas = ["🚨 <b>¡ACTUALIZACIÓN DE PLAZAS SISTEMA MAESTRO!</b> 🚨", ""]
    lineas.append(f"🌎 <b>Total plazas activas:</b> {total} {flecha}")
    lineas.append(f"🆕 <b>Plazas de hoy:</b> {hoy}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {ayer}")
    if total_mapa is not None and total_mapa != total:
        lineas.append(f"🗺️ <i>El mapa marca {total_mapa}; puede haber plazas aún sin cargar.</i>")
    lineas.append("")

    for titulo, items in (("🆕 <b>Plazas nuevas:</b>", cambios["nuevas"]),
                          ("❌ <b>Plazas eliminadas:</b>", cambios["eliminadas"]),
                          ("⌛ <b>Plazas vencidas:</b>", vencidas)):
        if items:
            lineas.append(titulo)
            for p in items[:15]:
                lineas.append(_resumen_corto(p))
            if len(items) > 15:
                lineas.append(f"  … y {len(items) - 15} más")
            lineas.append("")

    lineas.append("--- <b>TODAS LAS PLAZAS ACTIVAS</b> ---")
    lineas.append("")
    lineas.extend(_lineas_plazas(plazas_actuales, ids_nuevas))
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')
    return "\n".join(lineas)


def construir_resumen_filtrado(plazas, encabezado=None):
    hoy, ayer = contar_plazas_por_activacion(plazas)
    lineas = ["🚨 <b>¡Plazas Sistema Maestro!</b> 🚨", ""]
    if encabezado:
        lineas.append(f"🔎 <b>Filtro:</b> {html.escape(encabezado)}")
    lineas.append(f"🌎 <b>Total plazas activas:</b> {len(plazas)}")
    lineas.append(f"🆕 <b>Plazas de hoy:</b> {hoy}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {ayer}")
    lineas.append("")
    lineas.append("--- <b>PLAZAS</b> ---")
    lineas.append("")
    if not plazas:
        lineas.append("No se encontraron plazas para este filtro.")
        lineas.append("")
    else:
        lineas.extend(_lineas_plazas(plazas))
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')
    return "\n".join(lineas)


# ============================================================
# FLUJO PRINCIPAL DEL VIGILANTE
# ============================================================

def ejecutar_vigilante(notificar_siempre=False, chat_id=None):
    try:
        resultado = _ejecutar_vigilante(notificar_siempre, chat_id)
    except Exception as e:
        print(f"⚠️ Error en vigilante: {e}")
        enviar_error_limitado(str(e))
        resultado = f"Error: {str(e)[:100]}"
    try:
        set_meta("ultima_ejecucion", datetime.now(ZONA_COLOMBIA).isoformat())
        set_meta("ultimo_resultado", resultado)
    except Exception:
        pass
    return resultado


def _ejecutar_vigilante(notificar_siempre, chat_id):
    plazas_bd = cargar_datos_anteriores()
    primera_carga = len(plazas_bd) == 0

    vigentes, vencidas = limpiar_plazas_vencidas(plazas_bd)
    if vencidas:
        guardar_datos_actuales(vigentes)
    plazas_antes = [dict(p) for p in vigentes]

    sesion = nueva_sesion()
    info = obtener_info_mapa(sesion)
    if info["total"] == 0:
        return "El mapa no devolvió marcadores; ciclo omitido."

    errores = []
    for depto in info["conteo"].keys():
        try:
            plazas_depto = obtener_vacantes_por_departamento(depto)
            esperada = info["conteo_norm"].get(_norm(depto))
            with lock_db:  # cargar -> fusionar -> guardar de forma atómica
                bd = cargar_datos_anteriores()
                bd, _nuevas = fusionar_plazas_reconciliando_seguro(bd, plazas_depto, depto, esperada)
                guardar_datos_actuales(bd)
        except Exception as e:
            errores.append(depto)
            print(f"⚠️ Error scraping {depto}: {e}")

    plazas_actuales = cargar_datos_anteriores()
    set_meta("total_mapa", info["total"])
    cambios = detectar_cambios_completos(plazas_actuales, plazas_antes)

    hay_cambios = (cambios["total_nuevas"] > 0 or cambios["total_eliminadas"] > 0 or len(vencidas) > 0)

    if primera_carga and not notificar_siempre:
        return f"Base inicializada en silencio con {len(plazas_actuales)} plazas."

    if hay_cambios or notificar_siempre:
        resumen = construir_resumen_completo(plazas_actuales, plazas_antes, info["total"], cambios, vencidas)
        enviar_telegram(resumen, chat_id=chat_id)
        return "Notificación enviada." + (f" Errores en: {', '.join(errores)}" if errores else "")

    if chat_id is not None:
        enviar_telegram("✅ Vigilante ejecutado: no hay cambios nuevos respecto a la última revisión.", chat_id=chat_id)
    return "Sin cambios notificables." + (f" Errores en: {', '.join(errores)}" if errores else "")


def lanzar_vigilante_en_hilo(notificar_siempre=False, chat_id=None):
    """Intenta tomar el lock y correr el vigilante en segundo plano. False si ya hay uno corriendo."""
    if not lock_ejecucion_vigilante.acquire(blocking=False):
        return False

    def tarea():
        try:
            ejecutar_vigilante(notificar_siempre=notificar_siempre, chat_id=chat_id)
        finally:
            lock_ejecucion_vigilante.release()

    threading.Thread(target=tarea, daemon=True).start()
    return True


# ============================================================
# MENÚ INTERACTIVO (botones + respaldo por número)
# ============================================================

TECLADO_MENU = {"inline_keyboard": [
    [{"text": "📍 Departamento", "callback_data": "m:dep"},
     {"text": "📚 Áreas", "callback_data": "m:area"}],
    [{"text": "🔄 Actualizar", "callback_data": "m:act"}],
]}
TECLADO_VOLVER = {"inline_keyboard": [[{"text": "📋 Menú", "callback_data": "m:menu"}]]}


def obtener_departamentos_en_json():
    deptos = {(p.get("departamento") or "").strip() for p in cargar_datos_anteriores()}
    return sorted(d for d in deptos if d and d.lower() != "sin departamento")


def obtener_areas_en_json():
    areas = {(p.get("area") or "").strip() for p in cargar_datos_anteriores()}
    return sorted(a for a in areas if a and a.lower() != "sin área")


def _es_comando(texto, comandos):
    if not texto:
        return False
    limpio = texto.replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()
    return limpio in comandos


def _es_comando_menu(texto):
    return _es_comando(texto, ("menu", "menú", "/menu", "/menú", "/start"))


def _es_comando_actualizar(texto):
    return _es_comando(texto, ("actualizar", "/actualizar"))


def _enviar_menu_principal(chat_id):
    set_estado_menu(chat_id, "menu_principal")
    enviar_telegram(
        "📋 <b>Menú principal</b>\n\nElige una opción con los botones "
        "(o responde 1 = Departamento, 2 = Áreas, 3 = Actualizar).",
        chat_id=chat_id, reply_markup=TECLADO_MENU,
    )


def _enviar_lista(chat_id, tipo):
    if tipo == "departamento_lista":
        opciones, titulo, prefijo, etiquetas = obtener_departamentos_en_json(), "📍 <b>Elige un departamento:</b>", "d", None
    else:
        opciones, titulo, prefijo = obtener_areas_en_json(), "📚 <b>Elige un área:</b>", "a"
        etiquetas = [abreviar_area(o) for o in opciones]

    if not opciones:
        enviar_telegram("No hay datos guardados todavía. Escribe <b>Actualizar</b> primero.",
                        chat_id=chat_id, reply_markup=TECLADO_VOLVER)
        return

    set_estado_menu(chat_id, tipo, opciones)
    etiquetas = etiquetas or opciones
    botones = [{"text": f"{i}. {etq}"[:40], "callback_data": f"{prefijo}:{i}"}
               for i, etq in enumerate(etiquetas, start=1)]
    filas = [botones[i:i + 2] for i in range(0, len(botones), 2)]
    filas.append([{"text": "⬅️ Volver", "callback_data": "m:menu"}])
    enviar_telegram(titulo, chat_id=chat_id, reply_markup={"inline_keyboard": filas})


def _seleccionar(chat_id, tipo, seleccion):
    estado = get_estado_menu(chat_id)
    if not estado or estado["tipo"] != tipo:
        _enviar_lista(chat_id, tipo)  # el menú expiró o cambió: reenviar la lista
        return
    opciones = estado["opciones"]
    if not (1 <= seleccion <= len(opciones)):
        enviar_telegram(f"Opción inválida. Elige un número entre 1 y {len(opciones)}.", chat_id=chat_id)
        return
    nombre = opciones[seleccion - 1]
    if tipo == "departamento_lista":
        plazas = [p for p in cargar_datos_anteriores() if (p.get("departamento") or "").strip() == nombre]
        mensaje = construir_resumen_filtrado(plazas, f"Departamento: {nombre}")
    else:
        plazas = [p for p in cargar_datos_anteriores() if (p.get("area") or "").strip() == nombre]
        mensaje = construir_resumen_filtrado(plazas, f"Área: {nombre}")
    enviar_telegram(mensaje, chat_id=chat_id, reply_markup=TECLADO_VOLVER)


def _accion_actualizar(chat_id):
    if lanzar_vigilante_en_hilo(notificar_siempre=True, chat_id=chat_id):
        enviar_telegram("🔎 Actualizando plazas, dame un momento...", chat_id=chat_id)
    else:
        enviar_telegram("⏳ Ya hay una actualización en curso. Intenta de nuevo en un momento.", chat_id=chat_id)


def _manejar_callback(chat_id, data):
    if data == "m:menu":
        _enviar_menu_principal(chat_id)
    elif data == "m:dep":
        _enviar_lista(chat_id, "departamento_lista")
    elif data == "m:area":
        _enviar_lista(chat_id, "area_lista")
    elif data == "m:act":
        _accion_actualizar(chat_id)
    elif re.fullmatch(r"d:\d+", data):
        _seleccionar(chat_id, "departamento_lista", int(data.split(":")[1]))
    elif re.fullmatch(r"a:\d+", data):
        _seleccionar(chat_id, "area_lista", int(data.split(":")[1]))


def _procesar_seleccion_numerica(chat_id, texto):
    """Respaldo: si hay un menú vigente y el texto es un número, lo procesa. True si lo consumió."""
    texto = (texto or "").strip()
    if not re.fullmatch(r"\d+", texto):
        return False
    estado = get_estado_menu(chat_id, solo_vigente=True)
    if not estado:
        return False
    n = int(texto)
    if estado["tipo"] == "menu_principal":
        if n == 1:
            _enviar_lista(chat_id, "departamento_lista")
        elif n == 2:
            _enviar_lista(chat_id, "area_lista")
        elif n == 3:
            _accion_actualizar(chat_id)
        else:
            enviar_telegram("Opción inválida. Responde 1, 2 o 3.", chat_id=chat_id)
        return True
    if estado["tipo"] in ("departamento_lista", "area_lista"):
        _seleccionar(chat_id, estado["tipo"], n)
        return True
    return False


@app.route("/telegram-webhook", methods=["POST"])
def telegram_webhook():
    if TELEGRAM_WEBHOOK_SECRET:
        if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != TELEGRAM_WEBHOOK_SECRET:
            return {"ok": False}, 403

    # Siempre respondemos 200 para que Telegram no reintente en bucle.
    try:
        update = request.get_json(silent=True) or {}

        cq = update.get("callback_query")
        if cq:
            _api_telegram("answerCallbackQuery", {"callback_query_id": cq.get("id")})
            chat_id = ((cq.get("message") or {}).get("chat") or {}).get("id")
            if chat_id is not None:
                _manejar_callback(chat_id, cq.get("data", ""))
            return {"ok": True}, 200

        mensaje = update.get("message") or update.get("edited_message") or {}
        texto = mensaje.get("text", "")
        chat_id = (mensaje.get("chat") or {}).get("id")
        if chat_id is None:
            return {"ok": True}, 200

        if _es_comando_menu(texto):
            _enviar_menu_principal(chat_id)
        elif _procesar_seleccion_numerica(chat_id, texto):
            pass
        elif _es_comando_actualizar(texto):
            _accion_actualizar(chat_id)
    except Exception as e:
        print(f"⚠️ Error en webhook de Telegram: {e}")

    return {"ok": True}, 200


# ============================================================
# ENDPOINTS
# ============================================================

@app.route("/set-webhook")
def set_webhook():
    url_publica = request.host_url.rstrip("/").replace("http://", "https://", 1) + "/telegram-webhook"
    datos = {"url": url_publica,
             "allowed_updates": json.dumps(["message", "edited_message", "callback_query"])}
    if TELEGRAM_WEBHOOK_SECRET:
        datos["secret_token"] = TELEGRAM_WEBHOOK_SECRET
    r = _api_telegram("setWebhook", datos)
    _api_telegram("setMyCommands", {"commands": json.dumps([
        {"command": "menu", "description": "Abrir el menú de plazas"},
        {"command": "actualizar", "description": "Actualizar y ver todas las plazas"},
    ])})
    if r is None:
        return {"error": "No se pudo contactar a Telegram"}, 500
    return {"webhook_configurado": url_publica, "respuesta_telegram": r.json()}


@app.route("/check")
def check():
    if not lanzar_vigilante_en_hilo(notificar_siempre=False):
        return {"resultado": "Ya hay una ejecución en curso, se omitió este chequeo."}, 409
    return {"resultado": "Tarea iniciada en segundo plano"}, 202


@app.route("/check-force")
def check_force():
    if not lanzar_vigilante_en_hilo(notificar_siempre=True):
        return {"resultado": "Ya hay una ejecución en curso."}, 409
    return {"resultado": "Tarea iniciada; el resumen llegará a Telegram."}, 202


@app.route("/status")
def status():
    return {
        "db": DB_PATH,
        "plazas_en_db": len(cargar_datos_anteriores()),
        "ultima_ejecucion": get_meta("ultima_ejecucion"),
        "ultimo_resultado": get_meta("ultimo_resultado"),
        "total_mapa": get_meta("total_mapa"),
        "ejecutando_ahora": lock_ejecucion_vigilante.locked(),
    }


@app.route("/verjson")
def verjson():
    return {"ruta": DB_PATH, "contenido": cargar_datos_anteriores()}


@app.route("/departamentos")
def obtener_departamentos():
    try:
        info = obtener_info_mapa()
        if info["total"] == 0:
            return {"error": "No se encontraron departamentos"}, 404
        contador_json = Counter(_norm(p.get("departamento")) for p in cargar_datos_anteriores())
        deptos = [{"nombre": n, "cantidad": c, "en_json": contador_json.get(_norm(n), 0)}
                  for n, c in info["conteo"].items()]
        deptos.sort(key=lambda x: x["cantidad"], reverse=True)
        return {"departamentos": deptos, "total": info["total"], "departamentos_unicos": len(deptos)}
    except requests.exceptions.RequestException as e:
        return {"error": f"Error de conexión: {e}"}, 500
    except Exception as e:
        return {"error": f"Error inesperado: {e}"}, 500


@app.route("/agregar-departamento", methods=["POST"])
def agregar_departamento():
    try:
        data = request.get_json(silent=True)
        if not data or "departamento" not in data:
            return {"error": "Se requiere el nombre del departamento"}, 400
        nombre = data["departamento"].strip()

        try:
            plazas = obtener_vacantes_por_departamento(nombre)
        except ValueError as e:
            return {"error": str(e)}, 400
        if not plazas:
            return {"error": f"No se encontraron plazas para '{nombre}'."}, 404

        try:
            esperada = obtener_info_mapa()["conteo_norm"].get(_norm(nombre))
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            esperada = None

        with lock_db:
            bd = cargar_datos_anteriores()
            fusionadas, ids_nuevas = fusionar_plazas_reconciliando_seguro(bd, plazas, nombre, esperada)
            guardar_datos_actuales(fusionadas)

        return {
            "mensaje": f"✅ Se procesaron {len(plazas)} plazas de '{nombre}'",
            "plazas_encontradas": len(plazas),
            "total_plazas_en_json": len(fusionadas),
            "plazas_nuevas": len(ids_nuevas),
        }
    except Exception as e:
        return {"error": f"Error al agregar departamento: {e}"}, 500


@app.route("/limpiar-vencidas", methods=["POST"])
def limpiar_vencidas():
    try:
        with lock_db:
            plazas = cargar_datos_anteriores()
            vigentes, vencidas = limpiar_plazas_vencidas(plazas)
            if vencidas:
                guardar_datos_actuales(vigentes)
        return {"mensaje": f"Se eliminaron {len(vencidas)} plazas vencidas.",
                "eliminadas": len(vencidas), "restantes": len(vigentes)}
    except Exception as e:
        return {"error": str(e)}, 500


@app.route("/limpiar-json", methods=["POST"])
def limpiar_json():
    try:
        with db() as c:
            c.execute("DELETE FROM plazas")
            c.execute("DELETE FROM meta WHERE clave IN ('total_mapa')")
        return {"mensaje": "Base de plazas reiniciada. El próximo chequeo la repoblará en silencio."}
    except Exception as e:
        return {"error": f"Error al limpiar: {e}"}, 500


@app.route("/cargar-json", methods=["POST"])
def cargar_json():
    try:
        data = json.loads(request.get_data(as_text=True) or "")
    except json.JSONDecodeError as e:
        return {"error": f"El JSON es inválido: {e}"}, 400
    if not isinstance(data, list) or not data:
        return {"error": "El JSON debe ser una lista no vacía de objetos"}, 400
    if not all(isinstance(p, dict) and "id" in p and "departamento" in p for p in data):
        return {"error": "Cada objeto debe incluir al menos 'id' y 'departamento'"}, 400
    guardar_datos_actuales(data)
    return {"mensaje": f"✅ Guardadas {len(data)} plazas"}


PANEL_HTML = r"""<!DOCTYPE html>
<html><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Vigilante de Vacantes</title>
<style>
body{font-family:Arial,sans-serif;margin:20px;max-width:1000px}
button{padding:8px 14px;margin:4px;cursor:pointer;border:0;border-radius:4px;color:#fff;background:#007bff}
.ok{background:#28a745}.warn{background:#ffc107;color:#000}.bad{background:#dc3545}.info{background:#17a2b8}
.card{border:1px solid #ddd;padding:16px;margin-bottom:16px;border-radius:8px}
pre{background:#f4f4f4;padding:12px;border-radius:5px;overflow:auto;max-height:350px}
textarea{width:100%;font-family:monospace}
table{width:100%;border-collapse:collapse}th,td{padding:6px;border:1px solid #ddd;text-align:left}
</style></head><body>
<h1>🕵️ Vigilante de Vacantes</h1>
<div class="card">
<button onclick="run('/check')">🚀 Ejecutar (solo si hay cambios)</button>
<button class="ok" onclick="run('/check-force')">📢 Ejecutar (siempre notificar)</button>
<button class="info" onclick="verDeptos()">📍 Departamentos</button>
<button onclick="agregarTodos()">➕ Agregar pendientes</button>
<button class="bad" onclick="post('/limpiar-vencidas','¿Eliminar plazas vencidas?')">🗑️ Vencidas</button>
<button class="bad" onclick="post('/limpiar-json','¿Reiniciar TODA la base?')">🧨 Reiniciar base</button>
<div id="res" style="margin-top:8px"></div>
</div>
<div class="card" id="deptos" style="display:none"></div>
<div class="card"><h3>Plazas en la base</h3><pre id="json">Cargando...</pre></div>
<div class="card"><h3>Reemplazar base con JSON</h3>
<textarea id="txt" rows="6" placeholder="Lista de objetos con id y departamento"></textarea><br>
<button onclick="cargar()">📤 Cargar</button></div>
<script>
const res = m => document.getElementById('res').innerHTML = m;
function api(path, opts){
  return fetch(path, opts).then(r => r.json());
}
function run(p){ res('⏳ ...'); api(p).then(d => res(d.resultado || d.error)).catch(e => res('❌ ' + e)); }
function post(p, q){ if(!confirm(q)) return; api(p,{method:'POST'}).then(d => {res(d.mensaje || d.error); cargarJSON();}); }
function cargarJSON(){ api('/verjson').then(d => document.getElementById('json').textContent = JSON.stringify(d.contenido,null,2)); }
function verDeptos(){
  const c = document.getElementById('deptos'); c.style.display='block'; c.innerHTML='⏳ Cargando...';
  api('/departamentos').then(d => {
    if(d.error){ c.innerHTML = '❌ ' + d.error; return; }
    let h = `<p><b>Total (mapa):</b> ${d.total} — <b>Departamentos:</b> ${d.departamentos_unicos}</p><table><tr><th>Departamento</th><th>Mapa / Base</th><th></th></tr>`;
    d.departamentos.forEach(x => {
      const ok = x.en_json >= x.cantidad;
      h += `<tr><td>${x.nombre}</td><td>${x.cantidad} / ${x.en_json}</td><td>` +
           (ok ? '✅' : `<button class="warn" onclick="agregar('${x.nombre.replace(/'/g,"\\'")}')">Agregar</button>`) + `</td></tr>`;
    });
    c.innerHTML = h + '</table>';
  }).catch(e => c.innerHTML = '❌ ' + e);
}
function agregar(n){
  res('⏳ Agregando ' + n + '...');
  return api('/agregar-departamento',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({departamento:n})})
    .then(d => { res(d.mensaje || ('❌ ' + d.error)); verDeptos(); cargarJSON(); return d; });
}
async function agregarTodos(){
  const d = await api('/departamentos');
  if(d.error){ res('❌ ' + d.error); return; }
  const pend = d.departamentos.filter(x => x.en_json < x.cantidad);
  if(!pend.length){ res('✅ Todo está completo'); return; }
  if(!confirm('¿Agregar ' + pend.length + ' departamento(s)?')) return;
  for(const x of pend){ await agregar(x.nombre); }
  res('✅ Proceso terminado');
}
function cargar(){
  const t = document.getElementById('txt').value.trim();
  try{ JSON.parse(t); }catch(e){ alert('JSON inválido: ' + e.message); return; }
  api('/cargar-json',{method:'POST',headers:{'Content-Type':'application/json'},body:t})
    .then(d => { alert(d.mensaje || d.error); cargarJSON(); });
}
cargarJSON(); setInterval(cargarJSON, 30000);
</script></body></html>"""


@app.route("/")
def home():
    return PANEL_HTML


# ============================================================
# ARRANQUE
# ============================================================
# Sin hilos internos: el disparador es cron-job.org llamando a /check.
# Ejecutar con UN solo worker:
#   gunicorn app:app --workers 1 --threads 4 --timeout 120
init_db()
migrar_json_antiguo()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
