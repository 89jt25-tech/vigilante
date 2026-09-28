from flask import Flask, request
import requests
import os
import re
import json
import html
import threading
import time
from datetime import datetime, timedelta
from collections import defaultdict, Counter
from bs4 import BeautifulSoup
import xml.etree.ElementTree as ET
from zoneinfo import ZoneInfo

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 10 * 1024 * 1024  # 10 MB

TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ARCHIVO_DATOS = "plazas.json"
ARCHIVO_TOTAL_MAPA = "total_mapa.json"
ARCHIVO_ULTIMA_ACTUALIZACION = "ultima_actualizacion_completa.json"
ZONA_COLOMBIA = ZoneInfo("America/Bogota")

# ========== VENTANA PARA EL ICONO 🆕 ==========
# Una plaza se marca con 🆕 si lleva publicada entre MIN y MAX minutos.
# La fecha de publicación se calcula como: fecha_cierre - 24 horas.
#
# ⚠️ Ajusta estos valores según tu necesidad:
#   - MIN=2, MAX=3   → ventana original (frágil con scraping de 60s)
#   - MIN=2, MAX=30  → recomendado (tolerante a la latencia del scrape)
#   - MIN=0, MAX=30  → incluye también las recién publicadas
NUEVA_MIN_MINUTOS = int(os.environ.get("NUEVA_MIN_MINUTOS", 2))
NUEVA_MAX_MINUTOS = int(os.environ.get("NUEVA_MAX_MINUTOS", 30))

HEADERS_AJAX = {
    "accept": "application/xml, text/xml, */*; q=0.01",
    "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
    "faces-request": "partial/ajax",
    "x-requested-with": "XMLHttpRequest",
    "User-Agent": "Mozilla/5.0",
}

# ========== MAPEO DE DEPARTAMENTOS ==========
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


MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6

INTERVALO_ACTUALIZACION_POSTULADOS = int(os.environ.get("INTERVALO_ACTUALIZACION_POSTULADOS", 600))
INTERVALO_VIGILANTE_SEGUNDOS = int(os.environ.get("INTERVALO_VIGILANTE_SEGUNDOS", 60))

estado_vigilante_automatico = {
    "ultima_ejecucion": None,
    "ultimo_resultado": None,
    "ejecuciones": 0,
}
lock_estado_vigilante = threading.Lock()
lock_json = threading.RLock()

TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")

lock_ejecucion_vigilante = threading.Lock()

# ============================================================
# CARGA / GUARDADO DE DATOS (escritura atómica)
# ============================================================

def _escritura_atomica_json(ruta, data):
    tmp = f"{ruta}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.flush()
        try:
            os.fsync(f.fileno())
        except OSError:
            pass
    os.replace(tmp, ruta)


def cargar_datos_anteriores():
    with lock_json:
        if not os.path.exists(ARCHIVO_DATOS):
            return []
        try:
            with open(ARCHIVO_DATOS, "r", encoding="utf-8") as f:
                return json.load(f)
        except json.JSONDecodeError as e:
            print(f"❌ {ARCHIVO_DATOS} está corrupto (JSON inválido): {e}. Se devuelve lista vacía.")
            return []
        except Exception as e:
            print(f"❌ Error inesperado leyendo {ARCHIVO_DATOS}: {e}")
            return []


def guardar_datos_actuales(plazas):
    with lock_json:
        if plazas:
            _escritura_atomica_json(ARCHIVO_DATOS, plazas)
        else:
            print("⚠️ Se intentó guardar una lista vacía de plazas. No se sobrescribió el archivo.")


def obtener_total_plazas_mapa():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    coincidencias = re.findall(patron, r.text)
    if not coincidencias:
        print("⚠️ No se encontraron marcadores del mapa. ¿Cambió el HTML del sitio?")
    return len(coincidencias)


def guardar_total_mapa_actual(total_mapa):
    _escritura_atomica_json(ARCHIVO_TOTAL_MAPA, {"total_mapa": total_mapa})


def cargar_total_mapa_anterior():
    if os.path.exists(ARCHIVO_TOTAL_MAPA):
        try:
            with open(ARCHIVO_TOTAL_MAPA, "r", encoding="utf-8") as f:
                return json.load(f).get("total_mapa", 0)
        except Exception:
            return 0
    return 0


def guardar_ultima_actualizacion_completa(fecha):
    _escritura_atomica_json(ARCHIVO_ULTIMA_ACTUALIZACION, {"ultima": fecha.isoformat()})


def cargar_ultima_actualizacion_completa():
    if os.path.exists(ARCHIVO_ULTIMA_ACTUALIZACION):
        try:
            with open(ARCHIVO_ULTIMA_ACTUALIZACION, "r", encoding="utf-8") as f:
                return datetime.fromisoformat(json.load(f)["ultima"]).replace(tzinfo=ZONA_COLOMBIA)
        except Exception:
            return None
    return None


# ============================================================
# SCRAPING
# ============================================================

def obtener_viewstate(session):
    r = session.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
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


def parsear_vacantes(html_fragmento):
    soup = BeautifulSoup(html_fragmento, "html.parser")
    vacantes = []
    for panel in soup.select("div.vacante"):
        cargo = extraer_campo(panel, r"Cargo")
        postulados_texto = extraer_campo(panel, r"Postulados:")
        postulados = int(re.search(r"\d+", postulados_texto).group()) if postulados_texto else 0
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
    soup = BeautifulSoup(html_actual, 'html.parser')
    max_intentos = 50
    intentos = 0
    while intentos < max_intentos:
        enlaces = soup.select('div.vacante a.ui-commandlink')
        enlaces_ver = [a for a in enlaces if a.get_text(strip=True) == "Ver detalle"]
        if not enlaces_ver:
            break
        enlace = enlaces_ver[0]
        source_id = enlace.get('id')
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
        formulario = soup.find('form', id='form-busqueda')
        if formulario:
            for input_hidden in formulario.find_all('input', type='hidden'):
                name = input_hidden.get('name')
                value = input_hidden.get('value', '')
                if name and name not in data:
                    data[name] = value
        response = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
        resultado = extraer_actualizaciones(response.text)
        nuevo_viewstate = resultado.get("viewstate")
        if nuevo_viewstate:
            viewstate = nuevo_viewstate
        nuevo_html = resultado.get("html")
        if nuevo_html:
            html_actual = nuevo_html
        else:
            break
        soup = BeautifulSoup(html_actual, 'html.parser')
        intentos += 1
    return html_actual, viewstate


def desambiguar_ids(vacantes):
    conteo_total = Counter(v["id"] for v in vacantes)
    contador_visto = defaultdict(int)
    for v in vacantes:
        id_base = v["id"]
        if conteo_total[id_base] > 1:
            contador_visto[id_base] += 1
            v["id"] = f"{id_base}__{contador_visto[id_base]}"
    return vacantes


def cambiar_filtro_departamento(session, viewstate, codigo_departamento):
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:idInputDepartamento",
        "javax.faces.partial.execute": "@all",
        "javax.faces.partial.render": "accordion",
        "javax.faces.behavior.event": "change",
        "javax.faces.partial.event": "change",
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
        "form-busqueda:tabla-vacantes_rppDD": str(FILAS_POR_PAGINA),
    }
    r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
    resultado = extraer_actualizaciones(r.text)
    nuevo_viewstate = resultado["viewstate"] or viewstate
    return resultado["html"], nuevo_viewstate


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
        "form-busqueda:tabla-vacantes_rppDD": str(rows),
    }
    r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
    resultado = extraer_actualizaciones(r.text)
    nuevo_viewstate = resultado["viewstate"] or viewstate
    html_frag = resultado["html"]
    try:
        html_expandido, nuevo_viewstate = expandir_todos_detalles(session, nuevo_viewstate, html_frag)
        return html_expandido, nuevo_viewstate
    except Exception as e:
        print(f"⚠️ Error al expandir detalles en página {first//rows + 1}: {e}")
        return html_frag, nuevo_viewstate


def obtener_vacantes_por_departamento(nombre_departamento):
    nombre_clean = nombre_departamento.lower().strip()
    codigo = DEPARTAMENTOS_CODIGOS.get(nombre_clean)
    if not codigo:
        for key, value in DEPARTAMENTOS_CODIGOS.items():
            if nombre_clean in key or key in nombre_clean:
                codigo = value
                break
    if not codigo:
        raise ValueError(f"Departamento '{nombre_departamento}' no encontrado en el mapeo")

    session = requests.Session()
    viewstate = obtener_viewstate(session)
    if not viewstate:
        raise RuntimeError("No se pudo obtener el ViewState inicial")
    _, viewstate = cambiar_filtro_departamento(session, viewstate, codigo)
    todas = []
    first = 0
    for _ in range(MAX_PAGINAS):
        html_frag, viewstate = pedir_pagina_filtrada(session, viewstate, first, FILAS_POR_PAGINA, codigo)
        vacantes = parsear_vacantes(html_frag)
        if not vacantes:
            break
        todas.extend(vacantes)
        first += FILAS_POR_PAGINA
        if len(vacantes) < FILAS_POR_PAGINA:
            break
    return desambiguar_ids(todas)


def obtener_departamentos_del_mapa():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    titulos = re.findall(patron, r.text)
    return {t.split(" - ")[0].strip() for t in titulos if t}


def obtener_conteo_marcadores_por_departamento():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    titulos = re.findall(patron, r.text)
    contador = Counter()
    for t in titulos:
        contador[t.split(" - ")[0].strip()] += 1
    return contador


# ========== FUSIÓN DE PLAZAS ==========

def fusionar_plazas_reconciliando(plazas_bd, plazas_scrapeadas, departamento):
    ids_scrapeadas = {p["id"] for p in plazas_scrapeadas}
    conservadas = [p for p in plazas_bd if p.get("departamento") != departamento]
    bd_depto_por_id = {
        p["id"]: p for p in plazas_bd
        if p.get("departamento") == departamento and p["id"] in ids_scrapeadas
    }
    ids_nuevas = set()
    for p in plazas_scrapeadas:
        if p["id"] in bd_depto_por_id:
            bd_depto_por_id[p["id"]].update(p)
        else:
            bd_depto_por_id[p["id"]] = dict(p)
            ids_nuevas.add(p["id"])
    return conservadas + list(bd_depto_por_id.values()), ids_nuevas


def fusionar_plazas_reconciliando_seguro(plazas_bd, plazas_scrapeadas, departamento, cantidad_esperada=None):
    if cantidad_esperada is not None and len(plazas_scrapeadas) < cantidad_esperada:
        print(f"⚠️ Scrape incompleto de {departamento}: {len(plazas_scrapeadas)}/{cantidad_esperada}. Solo merge aditivo.")
        bd_por_id = {p["id"]: dict(p) for p in plazas_bd}
        ids_nuevas = set()
        for p in plazas_scrapeadas:
            if p["id"] in bd_por_id:
                bd_por_id[p["id"]].update(p)
            else:
                bd_por_id[p["id"]] = dict(p)
                ids_nuevas.add(p["id"])
        return list(bd_por_id.values()), ids_nuevas
    return fusionar_plazas_reconciliando(plazas_bd, plazas_scrapeadas, departamento)


# ========== HILO: REFRESCO DE POSTULADOS ==========

def obtener_departamentos_en_json():
    plazas = cargar_datos_anteriores()
    departamentos = set()
    for p in plazas:
        depto = (p.get("departamento") or "").strip()
        if depto and depto.lower() != "sin departamento":
            departamentos.add(depto)
    return sorted(departamentos)


def actualizar_postulados_departamento(nombre_departamento, conteo_mapa=None):
    plazas_scrapeadas = obtener_vacantes_por_departamento(nombre_departamento)
    if conteo_mapa is None:
        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            conteo_mapa = {}
    cantidad_esperada = conteo_mapa.get(nombre_departamento)
    with lock_json:
        plazas_bd = cargar_datos_anteriores()
        plazas_bd, ids_nuevas = fusionar_plazas_reconciliando_seguro(
            plazas_bd, plazas_scrapeadas, nombre_departamento, cantidad_esperada
        )
        guardar_datos_actuales(plazas_bd)
    return len(plazas_scrapeadas), len(ids_nuevas)


def hilo_actualizador_postulados():
    print(f"🧵 Hilo actualizador de postulados iniciado (cada {INTERVALO_ACTUALIZACION_POSTULADOS}s).")
    while True:
        adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
        if not adquirido:
            print("⏳ Hilo actualizador: el vigilante ya está scrapeando, se omite este ciclo.")
            time.sleep(INTERVALO_ACTUALIZACION_POSTULADOS)
            continue
        try:
            with lock_json:
                plazas_bd = cargar_datos_anteriores()
                vigentes, vencidas = limpiar_plazas_vencidas(plazas_bd)
                if vencidas:
                    guardar_datos_actuales(vigentes)
                    print(f"🗑️ {len(vencidas)} plaza(s) vencida(s) eliminada(s) automáticamente.")
            departamentos = obtener_departamentos_en_json()
            if departamentos:
                print(f"🔄 Refrescando postulados de {len(departamentos)} departamento(s).")
            try:
                conteo_mapa = obtener_conteo_marcadores_por_departamento()
            except Exception as e:
                print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
                conteo_mapa = {}
            for depto in departamentos:
                try:
                    encontradas, nuevas = actualizar_postulados_departamento(depto, conteo_mapa=conteo_mapa)
                    print(f"   ✔ {depto}: {encontradas} plazas revisadas, {nuevas} nueva(s)")
                except Exception as e:
                    print(f"   ✘ Error actualizando postulados de '{depto}': {e}")
        except Exception as e:
            print(f"⚠️ Error en hilo actualizador de postulados: {e}")
        finally:
            lock_ejecucion_vigilante.release()
        time.sleep(INTERVALO_ACTUALIZACION_POSTULADOS)


def hilo_vigilante_automatico():
    print(f"🧵 Hilo vigilante automático iniciado (cada {INTERVALO_VIGILANTE_SEGUNDOS}s).")
    time.sleep(5)
    while True:
        adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
        if not adquirido:
            time.sleep(INTERVALO_VIGILANTE_SEGUNDOS)
            continue
        try:
            resultado = ejecutar_vigilante(notificar_siempre=False)
            with lock_estado_vigilante:
                estado_vigilante_automatico["ultima_ejecucion"] = datetime.now(ZONA_COLOMBIA).isoformat()
                estado_vigilante_automatico["ultimo_resultado"] = resultado
                estado_vigilante_automatico["ejecuciones"] += 1
            print(f"🔍 Chequeo automático: {resultado}")
        except Exception as e:
            print(f"⚠️ Error en hilo vigilante automático: {e}")
        finally:
            lock_ejecucion_vigilante.release()
        time.sleep(INTERVALO_VIGILANTE_SEGUNDOS)


# ========== FECHAS Y VENTANA 🆕 ==========

def parsear_fecha_cierre(cierre_texto):
    if not cierre_texto:
        return None
    try:
        fecha_naive = datetime.strptime(cierre_texto.strip(), "%d/%m/%Y a las %H:%M")
        return fecha_naive.replace(tzinfo=ZONA_COLOMBIA)
    except ValueError:
        return None


def fecha_publicacion_de_plaza(plaza):
    """La publicación se asume 24 h antes del cierre."""
    fecha_cierre = parsear_fecha_cierre(plaza.get("cierre"))
    if not fecha_cierre:
        return None
    return fecha_cierre - timedelta(hours=24)


def minutos_desde_publicacion(plaza, ahora=None):
    """Devuelve los minutos transcurridos desde la publicación, o None si no se puede calcular."""
    if ahora is None:
        ahora = datetime.now(ZONA_COLOMBIA)
    fecha_pub = fecha_publicacion_de_plaza(plaza)
    if not fecha_pub:
        return None
    return (ahora - fecha_pub).total_seconds() / 60.0


def es_plaza_en_ventana_nueva(plaza, min_minutos=None, max_minutos=None, ahora=None):
    """
    True si la plaza lleva publicada entre min_minutos y max_minutos.
    La ventana está configurada por las variables de entorno
    NUEVA_MIN_MINUTOS y NUEVA_MAX_MINUTOS (defaults 2 y 30).
    """
    if min_minutos is None:
        min_minutos = NUEVA_MIN_MINUTOS
    if max_minutos is None:
        max_minutos = NUEVA_MAX_MINUTOS
    minutos = minutos_desde_publicacion(plaza, ahora=ahora)
    if minutos is None:
        return False
    return min_minutos <= minutos < max_minutos


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


# ========== FLUJO PRINCIPAL ==========

def ejecutar_vigilante(notificar_siempre=False, chat_id=None):
    try:
        plazas_bd = cargar_datos_anteriores()
        plazas_antes = [dict(p) for p in plazas_bd]

        plazas_vigentes, plazas_vencidas = limpiar_plazas_vencidas(plazas_bd)
        if plazas_vencidas:
            guardar_datos_actuales(plazas_vigentes)
            plazas_bd = plazas_vigentes

        total_mapa = obtener_total_plazas_mapa()
        total_mapa_anterior = cargar_total_mapa_anterior()

        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            conteo_mapa = {}

        print("🔄 Ejecutando scraping completo de todos los departamentos...")
        deptos_mapa = obtener_departamentos_del_mapa()
        ids_nuevas_totales = set()

        for depto in deptos_mapa:
            try:
                plazas_depto = obtener_vacantes_por_departamento(depto)
                cantidad_esperada = conteo_mapa.get(depto)
                plazas_bd, ids_nuevas_depto = fusionar_plazas_reconciliando_seguro(
                    plazas_bd, plazas_depto, depto, cantidad_esperada
                )
                ids_nuevas_totales |= ids_nuevas_depto
            except Exception as e:
                print(f"⚠️ Error scraping {depto}: {e}")

        # Diagnóstico: alertar si el JSON parece haberse reiniciado
        total_plazas_ahora = len(plazas_bd)
        if total_plazas_ahora > 0 and len(ids_nuevas_totales) >= total_plazas_ahora * 0.5 and total_plazas_ahora >= 5:
            print(
                f"🚨 ADVERTENCIA: {len(ids_nuevas_totales)} de {total_plazas_ahora} plazas "
                f"fueron detectadas como 'nuevas' en este ciclo. "
                f"¿El JSON se reinició o no está persistiendo entre ciclos?"
            )

        guardar_datos_actuales(plazas_bd)
        guardar_ultima_actualizacion_completa(datetime.now(ZONA_COLOMBIA))

        cambios = detectar_cambios_completos(plazas_bd, plazas_antes)
        hay_cambios = (
            cambios["total_nuevas"] > 0
            or cambios["total_eliminadas"] > 0
            or len(plazas_vencidas) > 0
        )
        debe_notificar = hay_cambios or notificar_siempre

        if debe_notificar:
            resumen = construir_resumen_completo(
                plazas_bd, plazas_antes, total_mapa, cambios, total_mapa_anterior
            )
            enviar_telegram(resumen, chat_id=chat_id)
            guardar_total_mapa_actual(total_mapa)
            return "Notificación enviada."
        else:
            if chat_id is not None:
                enviar_telegram(
                    "✅ Vigilante ejecutado: no hay cambios nuevos respecto a la última revisión.",
                    chat_id=chat_id,
                )
            guardar_total_mapa_actual(total_mapa)
            return "Sin cambios notificables."

    except Exception as e:
        mensaje_error = f"⚠️ Error en vigilante: {str(e)[:200]}"
        if chat_id is not None:
            try:
                enviar_telegram(mensaje_error, chat_id=chat_id)
            except Exception:
                pass
        else:
            print(mensaje_error)
        return f"Error: {str(e)[:100]}"


def construir_resumen_completo(plazas_actuales, plazas_anteriores, total_mapa, cambios, total_mapa_anterior):
    ahora = datetime.now(ZONA_COLOMBIA)
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_actuales)

    lineas = [
        "🚨 <b>¡ACTUALIZACIÓN DE PLAZAS SISTEMA MAESTRO!</b> 🚨",
        "",
    ]

    diferencia = total_mapa - total_mapa_anterior if total_mapa_anterior is not None else 0
    if diferencia > 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} <b>(+{diferencia})</b> ⬆️")
    elif diferencia < 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} <b>({diferencia})</b> ⬇️")
    else:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} ↔️")

    lineas += [
        f"🆕 <b>Plazas de hoy:</b> {total_hoy}",
        f"📅 <b>Plazas de ayer:</b> {total_ayer}",
        "",
    ]

    deptos = defaultdict(list)
    for p in plazas_actuales:
        deptos[p["departamento"]].append(p)

    lineas.append("--- <b>TODAS LAS PLAZAS ACTIVAS</b> ---")
    lineas.append("")
    for depto in sorted(deptos.keys()):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            area_esc = html.escape(abreviar_area(p["area"]))
            municipio_esc = html.escape(p["municipio"])
            zona_esc = html.escape(p["zona_tipo"])

            # 🆕 cuando la plaza lleva publicada en la ventana configurada.
            # La ventana por defecto es [2, 30) minutos (NUEVA_MIN_MINUTOS / NUEVA_MAX_MINUTOS).
            es_nueva = es_plaza_en_ventana_nueva(p, ahora=ahora)
            label = " 🆕" if es_nueva else ""
            lineas.append(f"  • {area_esc} ({municipio_esc} - {zona_esc}){label} – {p['postulados']} postulados")
        lineas.append("")

    lineas += ["", f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>']
    return "\n".join(lineas)


def detectar_cambios_completos(plazas_actuales, plazas_anteriores):
    anteriores_por_id = {p["id"]: p for p in plazas_anteriores}
    actuales_por_id = {p["id"]: p for p in plazas_actuales}
    nuevas, eliminadas, actualizadas = [], [], []
    for id_plaza, p_actual in actuales_por_id.items():
        if id_plaza not in anteriores_por_id:
            nuevas.append(p_actual)
        else:
            p_anterior = anteriores_por_id[id_plaza]
            if p_actual["postulados"] != p_anterior["postulados"]:
                actualizadas.append({
                    "id": id_plaza,
                    "departamento": p_actual["departamento"],
                    "area": p_actual["area"],
                    "postulados_anterior": p_anterior["postulados"],
                    "postulados_actual": p_actual["postulados"],
                })
    for id_plaza, p_anterior in anteriores_por_id.items():
        if id_plaza not in actuales_por_id:
            eliminadas.append(p_anterior)
    return {
        "nuevas": nuevas, "eliminadas": eliminadas, "actualizadas": actualizadas,
        "total_nuevas": len(nuevas), "total_eliminadas": len(eliminadas),
        "total_actualizadas": len(actualizadas),
    }


def contar_plazas_por_activacion(plazas):
    ahora = datetime.now(ZONA_COLOMBIA)
    hoy = ahora.date()
    ayer = hoy - timedelta(days=1)
    contador_hoy = contador_ayer = 0
    for p in plazas:
        fecha_cierre = parsear_fecha_cierre(p.get("cierre"))
        if fecha_cierre:
            fecha_activacion = fecha_cierre - timedelta(days=1)
            if fecha_activacion.date() == hoy:
                contador_hoy += 1
            elif fecha_activacion.date() == ayer:
                contador_ayer += 1
    return contador_hoy, contador_ayer


def enviar_telegram(mensaje, chat_id=None):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    LIMITE = 4000
    destino = chat_id if chat_id is not None else TELEGRAM_CHAT_ID
    for i, parte in enumerate(_dividir_mensaje(mensaje, LIMITE), start=1):
        try:
            r = requests.post(url, data={"chat_id": destino, "text": parte, "parse_mode": "HTML"}, timeout=10)
            if r.status_code != 200:
                print(f"⚠️ Error Telegram (parte {i}): {r.status_code} - {r.text}")
        except Exception as e:
            print(f"⚠️ Error Telegram (parte {i}): {e}")


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
            actual = ""
    if actual:
        partes.append(actual)
    return partes if partes else [mensaje[:limite]]


# ========== MENÚ INTERACTIVO POR TELEGRAM ==========

lock_estados_menu = threading.Lock()
estados_menu_chat = {}
MENU_TTL_SEGUNDOS = 3600


def _limpiar_menus_viejos():
    ahora = time.time()
    with lock_estados_menu:
        viejos = [cid for cid, est in estados_menu_chat.items()
                  if ahora - est.get("ultima_actividad", 0) > MENU_TTL_SEGUNDOS]
        for cid in viejos:
            estados_menu_chat.pop(cid, None)


def obtener_areas_en_json():
    plazas = cargar_datos_anteriores()
    areas = set()
    for p in plazas:
        area = (p.get("area") or "").strip()
        if area and area.lower() != "sin área":
            areas.add(area)
    return sorted(areas)


def filtrar_plazas_por_departamento(nombre_departamento):
    plazas = cargar_datos_anteriores()
    return [p for p in plazas if (p.get("departamento") or "").strip() == nombre_departamento]


def filtrar_plazas_por_area(nombre_area):
    plazas = cargar_datos_anteriores()
    return [p for p in plazas if (p.get("area") or "").strip() == nombre_area]


def construir_resumen_filtrado(plazas_filtradas, encabezado=None):
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_filtradas)
    deptos = defaultdict(list)
    for p in plazas_filtradas:
        deptos[p["departamento"]].append(p)
    lineas = ["🚨 <b>¡Plazas Sistema Maestro!</b> 🚨", ""]
    if encabezado:
        lineas.append(f"🔎 <b>Filtro:</b> {html.escape(encabezado)}")
    lineas += [
        f"🌎 <b>Total plazas activas:</b> {len(plazas_filtradas)}",
        f"🆕 <b>Plazas de hoy:</b> {total_hoy}",
        f"📅 <b>Plazas de ayer:</b> {total_ayer}",
        "", "--- <b>TODAS LAS PLAZAS</b> ---", "",
    ]
    if not deptos:
        lineas.append("No se encontraron plazas para este filtro.")
    else:
        for depto in sorted(deptos.keys()):
            lineas.append(f"📌 <b>{html.escape(depto)}</b>")
            for p in sorted(deptos[depto], key=lambda x: x["area"]):
                lineas.append(
                    f"  • {html.escape(abreviar_area(p['area']))} "
                    f"({html.escape(p['municipio'])} - {html.escape(p['zona_tipo'])}) "
                    f"– {p['postulados']} postulados"
                )
            lineas.append("")
    lineas += ["", f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>']
    return "\n".join(lineas)


def _es_comando_menu(texto):
    if not texto:
        return False
    candidato = texto.strip().replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()
    return candidato in ("menu", "menú", "/menu", "/menú")


def _enviar_menu_principal(chat_id):
    _limpiar_menus_viejos()
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": "menu_principal", "ultima_actividad": time.time()}
    enviar_telegram(
        "📋 <b>Menú principal</b>\n\n1. Departamento\n2. Áreas\n\nResponde con el número de la opción.",
        chat_id=chat_id,
    )


def _enviar_lista_departamentos(chat_id):
    departamentos = obtener_departamentos_en_json()
    if not departamentos:
        enviar_telegram("No hay departamentos con plazas guardadas todavía.", chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {
            "tipo": "departamento_lista",
            "opciones": departamentos,
            "ultima_actividad": time.time(),
        }
    lineas = ["📍 <b>Elige un departamento:</b>", ""]
    for i, nombre in enumerate(departamentos, start=1):
        lineas.append(f"{i}. {nombre}")
    lineas += ["", "Responde con el número."]
    enviar_telegram("\n".join(lineas), chat_id=chat_id)


def _enviar_lista_areas(chat_id):
    areas = obtener_areas_en_json()
    if not areas:
        enviar_telegram("No hay áreas con plazas guardadas todavía.", chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {
            "tipo": "area_lista",
            "opciones": areas,
            "ultima_actividad": time.time(),
        }
    lineas = ["📚 <b>Elige un área:</b>", ""]
    for i, nombre in enumerate(areas, start=1):
        lineas.append(f"{i}. {nombre}")
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
    with lock_estados_menu:
        if chat_id in estados_menu_chat:
            estados_menu_chat[chat_id]["ultima_actividad"] = time.time()
    seleccion = int(texto_limpio)
    tipo = estado["tipo"]
    if tipo == "menu_principal":
        if seleccion == 1:
            _enviar_lista_departamentos(chat_id)
        elif seleccion == 2:
            _enviar_lista_areas(chat_id)
        else:
            enviar_telegram("Opción inválida. Responde 1 o 2.", chat_id=chat_id)
        return True
    if tipo in ("departamento_lista", "area_lista"):
        opciones = estado.get("opciones", [])
        if not (1 <= seleccion <= len(opciones)):
            enviar_telegram(f"Opción inválida. Responde un número entre 1 y {len(opciones)}.", chat_id=chat_id)
            return True
        nombre_elegido = opciones[seleccion - 1]
        if tipo == "departamento_lista":
            plazas = filtrar_plazas_por_departamento(nombre_elegido)
            mensaje = construir_resumen_filtrado(plazas, encabezado=f"Departamento: {nombre_elegido}")
        else:
            plazas = filtrar_plazas_por_area(nombre_elegido)
            mensaje = construir_resumen_filtrado(plazas, encabezado=f"Área: {nombre_elegido}")
        enviar_telegram(mensaje, chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return True
    with lock_estados_menu:
        estados_menu_chat.pop(chat_id, None)
    return False


# ========== COMANDO "Actualizar" ==========

def _es_comando_actualizar(texto):
    if not texto:
        return False
    candidato = texto.strip().replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()
    return candidato in ("actualizar", "/actualizar")


def _procesar_comando_actualizar(chat_id):
    adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
    if not adquirido:
        enviar_telegram("⏳ Ya hay una actualización en curso. Te aviso cuando termine esa.", chat_id=chat_id)
        return
    try:
        enviar_telegram("🔎 Actualizando plazas, dame un momento...", chat_id=chat_id)
        ejecutar_vigilante(notificar_siempre=True, chat_id=chat_id)
    except Exception as e:
        enviar_telegram(f"⚠️ Error al actualizar: {str(e)[:200]}", chat_id=chat_id)
    finally:
        lock_ejecucion_vigilante.release()


@app.route("/telegram-webhook", methods=["POST"])
def telegram_webhook():
    if TELEGRAM_WEBHOOK_SECRET:
        if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != TELEGRAM_WEBHOOK_SECRET:
            return {"ok": False}, 403
    update = request.get_json(silent=True) or {}
    mensaje = update.get("message") or update.get("edited_message") or {}
    texto = mensaje.get("text", "")
    chat_id = (mensaje.get("chat") or {}).get("id")
    if chat_id is not None and _es_comando_menu(texto):
        _enviar_menu_principal(chat_id)
        return {"ok": True}, 200
    if chat_id is not None and _procesar_seleccion_menu(chat_id, texto):
        return {"ok": True}, 200
    if chat_id is not None and _es_comando_actualizar(texto):
        threading.Thread(target=_procesar_comando_actualizar, args=(chat_id,), daemon=True).start()
    return {"ok": True}, 200


@app.route("/set-webhook")
def set_webhook():
    url_publica = request.host_url.rstrip("/") + "/telegram-webhook"
    url_api = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/setWebhook"
    payload = {"url": url_publica}
    if TELEGRAM_WEBHOOK_SECRET:
        payload["secret_token"] = TELEGRAM_WEBHOOK_SECRET
    try:
        r = requests.post(url_api, data=payload, timeout=10)
        return {"webhook_configurado": url_publica, "respuesta_telegram": r.json()}
    except Exception as e:
        return {"error": str(e)}, 500


# ========== ENDPOINTS DE DIAGNÓSTICO ==========

@app.route("/check")
def check():
    adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
    if not adquirido:
        return {"resultado": "Ya hay una ejecución en curso."}, 409
    def tarea():
        try:
            ejecutar_vigilante(notificar_siempre=False)
        except Exception as e:
            print(f"Error en hilo de /check: {e}")
        finally:
            lock_ejecucion_vigilante.release()
    threading.Thread(target=tarea, daemon=True).start()
    return {"resultado": "Tarea iniciada en segundo plano"}, 202


@app.route("/check-force")
def check_force():
    return {"resultado": ejecutar_vigilante(notificar_siempre=True)}


@app.route("/status")
def status():
    with lock_estado_vigilante:
        return {
            "intervalo_segundos": INTERVALO_VIGILANTE_SEGUNDOS,
            "ventana_nueva_min_minutos": NUEVA_MIN_MINUTOS,
            "ventana_nueva_max_minutos": NUEVA_MAX_MINUTOS,
            "ultima_ejecucion": estado_vigilante_automatico["ultima_ejecucion"],
            "ultimo_resultado": estado_vigilante_automatico["ultimo_resultado"],
            "ejecuciones_desde_arranque": estado_vigilante_automatico["ejecuciones"],
        }


@app.route("/debug-nuevas")
def debug_nuevas():
    """
    Diagnóstico del icono 🆕. Muestra, para cada plaza guardada,
    cuándo se publicó (según cierre − 24 h), cuántos minutos han pasado,
    y si cumple la ventana configurada.
    """
    ahora = datetime.now(ZONA_COLOMBIA)
    plazas = cargar_datos_anteriores()
    filas = []
    for p in plazas:
        fecha_pub = fecha_publicacion_de_plaza(p)
        minutos = minutos_desde_publicacion(p, ahora=ahora)
        cumple = es_plaza_en_ventana_nueva(p, ahora=ahora)
        filas.append({
            "departamento": p.get("departamento"),
            "municipio": p.get("municipio"),
            "area": p.get("area"),
            "cierre": p.get("cierre"),
            "fecha_publicacion": fecha_pub.isoformat() if fecha_pub else None,
            "minutos_desde_publicacion": round(minutos, 2) if minutos is not None else None,
            "marcaria_nueva": cumple,
        })
    filas.sort(key=lambda x: (x["marcaria_nueva"] is False, x["minutos_desde_publicacion"] or 0))
    return {
        "ahora": ahora.isoformat(),
        "ventana_minutos": [NUEVA_MIN_MINUTOS, NUEVA_MAX_MINUTOS],
        "total_plazas": len(plazas),
        "plazas_que_se_marcarian_nuevas": sum(1 for f in filas if f["marcaria_nueva"]),
        "detalle": filas,
    }


@app.route("/")
def home():
    ruta = os.path.abspath(ARCHIVO_DATOS)
    contenido = "No existe"
    if os.path.exists(ruta):
        try:
            with open(ruta, "r", encoding="utf-8") as f:
                contenido = json.load(f)
        except Exception as e:
            contenido = f"Error leyendo JSON: {e}"

    html_page = """
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="UTF-8">
        <title>Vigilante de Vacantes</title>
        <style>
            body { font-family: Arial, sans-serif; margin: 30px; }
            button { padding: 10px 20px; margin: 5px; cursor: pointer; }
            pre { background: #f4f4f4; padding: 15px; border-radius: 5px; overflow: auto; max-height: 400px; }
            textarea { width: 100%; padding: 10px; font-family: monospace; }
            .card { border: 1px solid #ddd; padding: 20px; margin-bottom: 20px; border-radius: 8px; }
            .btn-primary { background-color: #007bff; color: white; border: none; }
            .btn-success { background-color: #28a745; color: white; border: none; }
            .btn-warning { background-color: #ffc107; color: black; border: none; }
            .btn-info { background-color: #17a2b8; color: white; border: none; }
            .btn-danger { background-color: #dc3545; color: white; border: none; }
            .btn-departamento { background-color: #6c757d; color: white; border: none; padding: 5px 10px; font-size: 12px; margin: 2px; }
            .btn-departamento:hover { background-color: #5a6268; }
            table { width: 100%; border-collapse: collapse; margin-top: 10px; }
            th, td { padding: 8px; border: 1px solid #ddd; text-align: left; }
            th { background-color: #f2f2f2; }
        </style>
    </head>
    <body>
        <h1>🕵️ Vigilante de Vacantes</h1>
        <div class="card">
            <h2>Acciones</h2>
            <button class="btn-primary" onclick="ejecutarCheck()">🚀 Ejecutar vigilante (notificar solo si hay cambios)</button>
            <button class="btn-success" onclick="ejecutarCheckForce()">📢 Ejecutar vigilante (SIEMPRE notificar)</button>
            <button class="btn-danger" onclick="limpiarJSON()">🗑️ Limpiar JSON (reiniciar base)</button>
            <button class="btn-info" onclick="verDepartamentos()">📍 Ver departamentos con plazas</button>
            <button class="btn-primary" onclick="agregarTodosLosDepartamentos()">🚀 Agregar todos los departamentos pendientes</button>
            <button class="btn-danger" onclick="limpiarVencidas()">🗑️ Eliminar plazas vencidas</button>
            <div id="resultado" style="margin-top: 10px; color: green;"></div>
        </div>
        <div class="card" id="departamentos-card" style="display: none;">
            <h2>📍 Departamentos con Plazas</h2>
            <div id="departamentos-content"></div>
        </div>
        <div class="card">
            <h2>Contenido del JSON (base de datos)</h2>
            <pre id="json-content">__CONTENIDO_JSON__</pre>
        </div>
        <div class="card">
            <h2>Cargar JSON manualmente</h2>
            <form id="cargaForm">
                <textarea name="json" rows="10" placeholder="Pega aquí el JSON (lista de objetos)"></textarea><br>
                <button type="submit">📤 Cargar JSON</button>
            </form>
        </div>
        <script>
            function ejecutarCheck() {
                fetch('/check').then(r => r.json()).then(d => {
                    document.getElementById('resultado').innerHTML = '✅ ' + d.resultado;
                }).catch(e => {
                    document.getElementById('resultado').innerHTML = '❌ Error: ' + e;
                });
            }
            function ejecutarCheckForce() {
                document.getElementById('resultado').innerHTML = '⏳ Enviando notificación...';
                fetch('/check-force').then(r => r.json()).then(d => {
                    document.getElementById('resultado').innerHTML = '✅ ' + d.resultado;
                }).catch(e => {
                    document.getElementById('resultado').innerHTML = '❌ Error: ' + e;
                });
            }
            function verDepartamentos() {
                const card = document.getElementById('departamentos-card');
                const content = document.getElementById('departamentos-content');
                card.style.display = 'block';
                content.innerHTML = '⏳ Cargando departamentos...';
                fetch('/departamentos').then(r => r.json()).then(data => {
                    if (data.error) { content.innerHTML = `❌ ${data.error}`; return; }
                    let html = `<p><b>Total plazas (mapa):</b> ${data.total}</p>
                        <p><b>Departamentos únicos:</b> ${data.departamentos_unicos}</p><br>
                        <table><thead><tr><th>Departamento</th><th style="text-align:center;">Cantidad</th><th style="text-align:center;">Acción</th></tr></thead><tbody>`;
                    data.departamentos.forEach((d, i) => {
                        const bg = i % 2 === 0 ? '#ffffff' : '#f9f9f9';
                        const completo = d.en_json >= d.cantidad;
                        const cls = completo ? 'btn-success' : 'btn-warning';
                        const txt = completo ? '✅ Completo' : `📥 Agregar ${d.cantidad} plazas`;
                        const dis = completo ? 'disabled' : '';
                        html += `<tr style="background-color:${bg};"><td><b>${d.nombre}</b></td>
                            <td style="text-align:center;"><b>${d.cantidad}</b> (JSON: ${d.en_json})</td>
                            <td style="text-align:center;"><button class="btn-departamento ${cls}" onclick="agregarDepartamento('${d.nombre}')" ${dis}>${txt}</button></td></tr>`;
                    });
                    html += `</tbody></table><br><button onclick="document.getElementById('departamentos-card').style.display='none'">Cerrar</button>`;
                    content.innerHTML = html;
                }).catch(e => { content.innerHTML = `❌ Error: ${e}`; });
            }
            function actualizarContenidoJSON() {
                fetch('/verjson', { cache: 'no-store' }).then(r => r.json()).then(d => {
                    const pre = document.getElementById('json-content');
                    if (pre) pre.textContent = JSON.stringify(d.contenido, null, 2);
                }).catch(e => console.error(e));
            }
            setInterval(actualizarContenidoJSON, 30000);
            function agregarDepartamento(departamento) {
                if (!confirm(`¿Agregar todas las plazas de "${departamento}" al JSON?`)) return;
                const div = document.getElementById('resultado');
                div.innerHTML = `⏳ Agregando plazas de ${departamento}...`;
                fetch('/agregar-departamento', {
                    method: 'POST', headers: {'Content-Type': 'application/json'},
                    body: JSON.stringify({ departamento })
                }).then(r => r.json()).then(d => {
                    if (d.error) { div.innerHTML = `❌ ${d.error}`; alert(`❌ ${d.error}`); }
                    else {
                        div.innerHTML = `✅ ${d.mensaje} (Total en JSON: ${d.total_plazas_en_json})`;
                        alert(`✅ ${d.mensaje}\\nEncontradas: ${d.plazas_encontradas}\\nNuevas: ${d.plazas_nuevas}`);
                        verDepartamentos(); actualizarContenidoJSON();
                    }
                }).catch(e => { div.innerHTML = `❌ Error: ${e}`; alert(`❌ ${e}`); });
            }
            function limpiarJSON() {
                if (!confirm('⚠️ ¿Eliminar TODOS los datos guardados?')) return;
                const div = document.getElementById('resultado');
                div.innerHTML = '⏳ Eliminando...';
                fetch('/limpiar-json', { method: 'POST' }).then(r => r.json()).then(d => {
                    if (d.error) { div.innerHTML = '❌ ' + d.error; alert('❌ ' + d.error); }
                    else { div.innerHTML = '✅ ' + d.mensaje; alert('✅ ' + d.mensaje); location.reload(); }
                }).catch(e => { div.innerHTML = '❌ ' + e; alert('❌ ' + e); });
            }
            function agregarTodosLosDepartamentos() {
                if (!confirm('⚠️ ¿Agregar plazas de TODOS los departamentos pendientes?')) return;
                const btn = document.querySelector('button[onclick="agregarTodosLosDepartamentos()"]');
                btn.disabled = true; btn.textContent = '⏳ Procesando...';
                const div = document.getElementById('resultado');
                div.innerHTML = '⏳ Obteniendo departamentos...';
                fetch('/departamentos').then(r => r.json()).then(data => {
                    if (data.error) { div.innerHTML = `❌ ${data.error}`; btn.disabled = false; btn.textContent = '🚀 Agregar todos'; return; }
                    const pendientes = data.departamentos.filter(d => d.en_json < d.cantidad);
                    if (pendientes.length === 0) { div.innerHTML = '✅ Todos completos.'; btn.disabled = false; btn.textContent = '🚀 Agregar todos'; return; }
                    let proc = 0, total = 0, errs = [];
                    function sig() {
                        if (proc >= pendientes.length) {
                            const msg = `✅ Completado. ${total} depto(s) procesados. ${errs.length ? errs.length + ' error(es).' : ''}`;
                            div.innerHTML = msg; alert(msg);
                            verDepartamentos(); actualizarContenidoJSON();
                            btn.disabled = false; btn.textContent = '🚀 Agregar todos';
                            return;
                        }
                        const nombre = pendientes[proc].nombre;
                        div.innerHTML = `⏳ ${nombre} (${proc+1}/${pendientes.length})...`;
                        fetch('/agregar-departamento', {
                            method: 'POST', headers: {'Content-Type': 'application/json'},
                            body: JSON.stringify({ departamento: nombre })
                        }).then(r => r.json()).then(d => {
                            if (d.error) errs.push(`❌ ${nombre}: ${d.error}`); else total++;
                            proc++; sig();
                        }).catch(e => { errs.push(`❌ ${nombre}: ${e.message}`); proc++; sig(); });
                    }
                    sig();
                }).catch(e => { div.innerHTML = `❌ ${e}`; btn.disabled = false; btn.textContent = '🚀 Agregar todos'; });
            }
            function limpiarVencidas() {
                if (!confirm('⚠️ ¿Eliminar plazas con cierre ya pasado?')) return;
                const div = document.getElementById('resultado');
                div.innerHTML = '⏳ Eliminando vencidas...';
                fetch('/limpiar-vencidas', { method: 'POST', headers: {'Content-Type': 'application/json'}
                }).then(r => r.json()).then(d => {
                    if (d.error) { div.innerHTML = `❌ ${d.error}`; alert(`❌ ${d.error}`); }
                    else { div.innerHTML = `✅ ${d.mensaje} (Restantes: ${d.restantes || 0})`; alert(`✅ ${d.mensaje}`); verDepartamentos(); actualizarContenidoJSON(); }
                }).catch(e => { div.innerHTML = `❌ ${e}`; alert(`❌ ${e}`); });
            }
            document.getElementById('cargaForm').addEventListener('submit', function(e) {
                e.preventDefault();
                const jsonStr = this.querySelector('textarea').value.trim();
                if (!jsonStr) { alert('❌ Pega un JSON.'); return; }
                try { JSON.parse(jsonStr); } catch (err) { alert('❌ JSON inválido: ' + err.message); return; }
                fetch('/cargar-json', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: jsonStr })
                    .then(r => r.json()).then(d => {
                        alert('✅ ' + (d.mensaje || d.error));
                        if (d.mensaje) location.reload();
                    }).catch(e => alert('❌ ' + e));
            });
        </script>
    </body>
    </html>
    """
    html_page = html_page.replace(
        "__CONTENIDO_JSON__",
        html.escape(json.dumps(contenido, indent=2, ensure_ascii=False))
    )
    return html_page


@app.route("/limpiar-json", methods=["POST"])
def limpiar_json():
    try:
        mensaje = ""
        for ruta, nombre in [(ARCHIVO_DATOS, "plazas.json"), (ARCHIVO_TOTAL_MAPA, "total_mapa.json")]:
            if os.path.exists(ruta):
                os.remove(ruta)
                mensaje += f" {nombre} eliminado."
            else:
                mensaje += f" {nombre} ya no existía."
        return {"mensaje": mensaje.strip()}, 200
    except Exception as e:
        return {"error": f"Error al limpiar JSON: {str(e)}"}, 500


@app.route("/cargar-json", methods=["POST"])
def cargar_json():
    try:
        raw = request.get_data(as_text=True)
        if not raw:
            return {"error": "El cuerpo está vacío"}, 400
        data = json.loads(raw)
    except json.JSONDecodeError as e:
        return {"error": f"JSON inválido: {str(e)}"}, 400
    if not isinstance(data, list) or not data:
        return {"error": "El JSON debe ser una lista no vacía"}, 400
    guardar_datos_actuales(data)
    try:
        guardar_total_mapa_actual(obtener_total_plazas_mapa())
    except Exception as e:
        print(f"Error al actualizar total mapa: {e}")
    return {"mensaje": f"✅ JSON guardado ({len(data)} plazas)"}


@app.route("/verjson")
def verjson():
    ruta = os.path.abspath(ARCHIVO_DATOS)
    if os.path.exists(ruta):
        try:
            with open(ruta, "r", encoding="utf-8") as f:
                return {"ruta": ruta, "contenido": json.load(f)}
        except Exception as e:
            return {"ruta": ruta, "contenido": f"Error: {e}"}
    return {"ruta": ruta, "contenido": "Archivo no existe"}


@app.route("/departamentos")
def obtener_departamentos():
    try:
        response = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
        response.raise_for_status()
        patron = r'L\.marker\(\[.*?\],\s*\{[^}]*title:\s*[\'"]([^\'"]+)[\'"][^}]*\}\)'
        coincidencias = re.findall(patron, response.text, re.DOTALL)
        if not coincidencias:
            coincidencias = re.findall(r'title:\s*[\'"]([^\'"]+)[\'"]', response.text, re.DOTALL)
        if not coincidencias:
            return {"error": "No se encontraron departamentos"}, 404
        contador_mapa = Counter(coincidencias)
        contador_json = defaultdict(int)
        for p in cargar_datos_anteriores():
            depto = p.get("departamento", "").strip()
            if depto:
                contador_json[depto] += 1
        departamentos = []
        for nombre, cantidad_mapa in contador_mapa.items():
            nombre_depto = nombre.split(" - ")[0].strip()
            departamentos.append({
                "nombre": nombre_depto,
                "cantidad": cantidad_mapa,
                "en_json": contador_json.get(nombre_depto, 0),
            })
        departamentos.sort(key=lambda x: x["cantidad"], reverse=True)
        return {
            "departamentos": departamentos,
            "total": len(coincidencias),
            "departamentos_unicos": len(departamentos),
        }
    except requests.exceptions.RequestException as e:
        return {"error": f"Error de conexión: {str(e)}"}, 500
    except Exception as e:
        return {"error": f"Error inesperado: {str(e)}"}, 500


@app.route("/agregar-departamento", methods=["POST"])
def agregar_departamento():
    try:
        data = request.get_json()
        if not data or "departamento" not in data:
            return {"error": "Se requiere el nombre del departamento"}, 400
        nombre = data["departamento"].strip()
        try:
            plazas_dep = obtener_vacantes_por_departamento(nombre)
        except ValueError as e:
            return {"error": str(e)}, 400
        if not plazas_dep:
            return {"error": f"No se encontraron plazas para '{nombre}'."}, 404
        try:
            conteo = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            conteo = {}
        with lock_json:
            plazas_bd = cargar_datos_anteriores()
            fusionadas, nuevas = fusionar_plazas_reconciliando_seguro(
                plazas_bd, plazas_dep, nombre, conteo.get(nombre)
            )
            guardar_datos_actuales(fusionadas)
        try:
            guardar_total_mapa_actual(obtener_total_plazas_mapa())
        except Exception as e:
            print(f"Error al actualizar total_mapa: {e}")
        return {
            "mensaje": f"✅ Se procesaron {len(plazas_dep)} plazas de '{nombre}'",
            "plazas_encontradas": len(plazas_dep),
            "total_plazas_en_json": len(fusionadas),
            "plazas_nuevas": len(nuevas),
        }
    except Exception as e:
        return {"error": f"Error al agregar departamento: {str(e)}"}, 500


@app.route("/limpiar-vencidas", methods=["POST"])
def limpiar_vencidas():
    try:
        with lock_json:
            plazas = cargar_datos_anteriores()
            if not plazas:
                return {"mensaje": "No hay plazas en el JSON", "eliminadas": 0}, 200
            vigentes, vencidas = limpiar_plazas_vencidas(plazas)
            if vencidas:
                guardar_datos_actuales(vigentes)
                return {"mensaje": f"Se eliminaron {len(vencidas)} plazas vencidas.",
                        "eliminadas": len(vencidas), "restantes": len(vigentes)}, 200
            return {"mensaje": "No hay plazas vencidas.", "eliminadas": 0}, 200
    except Exception as e:
        return {"error": str(e)}, 500


# Arranca los hilos al importar el módulo.
# ⚠️ Usa `gunicorn app:app --workers 1`. Con más de 1 worker, estos hilos
# arrancan UNA VEZ POR WORKER y terminan scrapeando/notificando de más.
threading.Thread(target=hilo_actualizador_postulados, daemon=True).start()
threading.Thread(target=hilo_vigilante_automatico, daemon=True).start()


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
