from flask import Flask, request
import requests
import os
import re
import json
import html
import base64
import threading
import time
from datetime import datetime, timedelta
from collections import defaultdict, Counter
from bs4 import BeautifulSoup
import xml.etree.ElementTree as ET
from zoneinfo import ZoneInfo

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 10 * 1024 * 1024

TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ARCHIVO_DATOS = "plazas.json"
ARCHIVO_TOTAL_MAPA = "total_mapa.json"
ARCHIVO_CONTEO_DEPTOS = "conteo_deptos.json"
ARCHIVO_ULTIMA_ACTUALIZACION = "ultima_actualizacion_completa.json"
ZONA_COLOMBIA = ZoneInfo("America/Bogota")

GITHUB_REPO = os.environ["GITHUB_REPO"]
GITHUB_TOKEN = os.environ["GITHUB_TOKEN"]
GITHUB_BRANCH = os.environ.get("GITHUB_BRANCH", "main")
GITHUB_DATA_DIR = os.environ.get("GITHUB_DATA_DIR", "datos")

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

MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6

INTERVALO_ACTUALIZACION_POSTULADOS = int(os.environ.get("INTERVALO_ACTUALIZACION_POSTULADOS", 600))
INTERVALO_VIGILANTE_SEGUNDOS = int(os.environ.get("INTERVALO_VIGILANTE_SEGUNDOS", 60))

estado_vigilante_automatico = {"ultima_ejecucion": None, "ultimo_resultado": None, "ejecuciones": 0}
lock_estado_vigilante = threading.Lock()
lock_json = threading.RLock()
TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")
lock_ejecucion_vigilante = threading.Lock()


# ========== HELPERS GITHUB ==========

def _gh_headers():
    return {"Authorization": f"token {GITHUB_TOKEN}",
            "Accept": "application/vnd.github.v3+json"}

def _gh_path(nombre):
    return f"{GITHUB_DATA_DIR}/{nombre}" if GITHUB_DATA_DIR else nombre

def github_leer_archivo(nombre):
    url = f"https://api.github.com/repos/{GITHUB_REPO}/contents/{_gh_path(nombre)}"
    r = requests.get(url, headers=_gh_headers(), params={"ref": GITHUB_BRANCH}, timeout=20)
    if r.status_code == 404:
        return None, None
    r.raise_for_status()
    data = r.json()
    return base64.b64decode(data["content"]).decode("utf-8"), data["sha"]

def github_escribir_archivo(nombre, contenido_str, mensaje="Actualizar datos"):
    url = f"https://api.github.com/repos/{GITHUB_REPO}/contents/{_gh_path(nombre)}"
    _, sha = github_leer_archivo(nombre)
    payload = {"message": mensaje,
               "content": base64.b64encode(contenido_str.encode("utf-8")).decode("ascii"),
               "branch": GITHUB_BRANCH}
    if sha:
        payload["sha"] = sha
    r = requests.put(url, headers=_gh_headers(), json=payload, timeout=20)
    r.raise_for_status()
    return r.json()

def github_eliminar_archivo(nombre, mensaje="Eliminar datos"):
    url = f"https://api.github.com/repos/{GITHUB_REPO}/contents/{_gh_path(nombre)}"
    _, sha = github_leer_archivo(nombre)
    if not sha:
        return False
    r = requests.delete(url, headers=_gh_headers(),
                        json={"message": mensaje, "sha": sha, "branch": GITHUB_BRANCH},
                        timeout=20)
    r.raise_for_status()
    return True


# ========== CARGA / GUARDADO ==========

def cargar_datos_anteriores():
    with lock_json:
        try:
            contenido, _ = github_leer_archivo(ARCHIVO_DATOS)
            if contenido:
                return json.loads(contenido)
        except Exception as e:
            print(f"⚠️ Error leyendo {ARCHIVO_DATOS}: {e}")
        return []

def guardar_datos_actuales(plazas):
    with lock_json:
        if not plazas:
            print("⚠️ Lista vacía, no se guarda.")
            return
        try:
            nuevo = json.dumps(plazas, ensure_ascii=False, indent=2)
            actual, _ = github_leer_archivo(ARCHIVO_DATOS)
            if actual == nuevo:
                return
            github_escribir_archivo(ARCHIVO_DATOS, nuevo, "Actualizar plazas.json")
        except Exception as e:
            print(f"⚠️ Error guardando {ARCHIVO_DATOS}: {e}")

def obtener_total_plazas_mapa():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    return len(re.findall(r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'", r.text))

def guardar_total_mapa_actual(total_mapa):
    try:
        github_escribir_archivo(ARCHIVO_TOTAL_MAPA,
                                json.dumps({"total_mapa": total_mapa}, ensure_ascii=False, indent=2),
                                "Actualizar total_mapa.json")
    except Exception as e:
        print(f"⚠️ Error guardando total_mapa: {e}")

def cargar_total_mapa_anterior():
    try:
        contenido, _ = github_leer_archivo(ARCHIVO_TOTAL_MAPA)
        if contenido:
            return json.loads(contenido).get("total_mapa", 0)
    except Exception as e:
        print(f"⚠️ Error leyendo total_mapa: {e}")
    return 0

def guardar_ultima_actualizacion_completa(fecha):
    try:
        github_escribir_archivo(ARCHIVO_ULTIMA_ACTUALIZACION,
                                json.dumps({"ultima": fecha.isoformat()}),
                                "Actualizar ultima_actualizacion")
    except Exception as e:
        print(f"⚠️ Error guardando ultima_actualizacion: {e}")

def cargar_conteo_deptos_anterior():
    try:
        contenido, _ = github_leer_archivo(ARCHIVO_CONTEO_DEPTOS)
        if contenido:
            return json.loads(contenido)
    except Exception as e:
        print(f"⚠️ Error leyendo conteo_deptos: {e}")
    return {}

def guardar_conteo_deptos(conteo):
    try:
        nuevo = json.dumps(conteo, ensure_ascii=False, indent=2, sort_keys=True)
        actual, _ = github_leer_archivo(ARCHIVO_CONTEO_DEPTOS)
        if actual == nuevo:
            return
        github_escribir_archivo(ARCHIVO_CONTEO_DEPTOS, nuevo, "Actualizar conteo_deptos.json")
    except Exception as e:
        print(f"⚠️ Error guardando conteo_deptos: {e}")


# ========== SCRAPING ==========

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
        uid = update.get("id") or ""
        contenido = update.text or ""
        if uid == "javax.faces.ViewState":
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
        zona_geo = zonas[0].get_text(strip=True).replace("Zona:", "").strip() if zonas else "Sin zona"
        zona_tipo = zonas[1].get_text(strip=True).replace("Zona:", "").strip().capitalize() if len(zonas) > 1 else "Sin tipo"
        departamento = extraer_campo(panel, r"Departamento:")
        municipio = extraer_campo(panel, r"Municipio:")
        id_plaza = f"{departamento}|{area}|{zona_geo}|{municipio}|{cierre}|{secretaria}|{cargo}|{tipo}".lower().replace(" ", "_")
        vacantes.append({
            "id": id_plaza,
            "area": area or "Sin área",
            "secretaria": secretaria or "Sin secretaría",
            "zona": zona_geo,
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
    for _ in range(50):
        enlaces = soup.select('div.vacante a.ui-commandlink')
        enlaces_ver = [a for a in enlaces if a.get_text(strip=True) == "Ver detalle"]
        if not enlaces_ver:
            break
        source_id = enlaces_ver[0].get('id')
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
            for inp in formulario.find_all('input', type='hidden'):
                n = inp.get('name'); v = inp.get('value', '')
                if n and n not in data:
                    data[n] = v
        response = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
        resultado = extraer_actualizaciones(response.text)
        if resultado.get("viewstate"):
            viewstate = resultado["viewstate"]
        if resultado.get("html"):
            html_actual = resultado["html"]
        else:
            break
        soup = BeautifulSoup(html_actual, 'html.parser')
    return html_actual, viewstate

def desambiguar_ids(vacantes):
    conteo = Counter(v["id"] for v in vacantes)
    visto = defaultdict(int)
    for v in vacantes:
        if conteo[v["id"]] > 1:
            visto[v["id"]] += 1
            v["id"] = f"{v['id']}__{visto[v['id']]}"
    return vacantes

def cambiar_filtro_departamento(session, viewstate, codigo):
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
        "form-busqueda:idInputDepartamento_input": codigo,
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
    res = extraer_actualizaciones(r.text)
    return res["html"], res["viewstate"] or viewstate

def pedir_pagina_filtrada(session, viewstate, first, rows, codigo):
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
        "form-busqueda:idInputDepartamento_input": codigo,
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
    res = extraer_actualizaciones(r.text)
    vst = res["viewstate"] or viewstate
    try:
        return expandir_todos_detalles(session, vst, res["html"])
    except Exception as e:
        print(f"⚠️ Error expandiendo detalles: {e}")
        return res["html"], vst

def obtener_vacantes_por_departamento(nombre_departamento):
    nc = nombre_departamento.lower().strip()
    codigo = DEPARTAMENTOS_CODIGOS.get(nc)
    if not codigo:
        for k, v in DEPARTAMENTOS_CODIGOS.items():
            if nc in k or k in nc:
                codigo = v
                break
    if not codigo:
        raise ValueError(f"Departamento '{nombre_departamento}' no encontrado")
    session = requests.Session()
    vst = obtener_viewstate(session)
    if not vst:
        raise RuntimeError("Sin ViewState inicial")
    _, vst = cambiar_filtro_departamento(session, vst, codigo)
    todas = []
    first = 0
    for _ in range(MAX_PAGINAS):
        html_frag, vst = pedir_pagina_filtrada(session, vst, first, FILAS_POR_PAGINA, codigo)
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
    titulos = re.findall(r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'", r.text)
    return {t.split(" - ")[0].strip() for t in titulos if t}

def obtener_conteo_marcadores_por_departamento():
    """Una sola petición al mapa. Devuelve dict {depto: cantidad}."""
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    titulos = re.findall(r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'", r.text)
    return dict(Counter(t.split(" - ")[0].strip() for t in titulos))

def fusionar_plazas_reconciliando(plazas_bd, plazas_scrapeadas, departamento):
    ids_scrapeadas = {p["id"] for p in plazas_scrapeadas}
    conservadas = [p for p in plazas_bd if p.get("departamento") != departamento]
    bd_depto = {p["id"]: p for p in plazas_bd
                if p.get("departamento") == departamento and p["id"] in ids_scrapeadas}
    ids_nuevas = set()
    for p in plazas_scrapeadas:
        if p["id"] in bd_depto:
            bd_depto[p["id"]].update(p)
        else:
            bd_depto[p["id"]] = dict(p)
            ids_nuevas.add(p["id"])
    return conservadas + list(bd_depto.values()), ids_nuevas

def fusionar_plazas_reconciliando_seguro(plazas_bd, plazas_scrapeadas, departamento, cantidad_esperada=None):
    if cantidad_esperada is not None and len(plazas_scrapeadas) < cantidad_esperada:
        print(f"⚠️ Scrape incompleto {departamento}: {len(plazas_scrapeadas)}/{cantidad_esperada}")
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

def obtener_departamentos_en_json():
    return sorted({(p.get("departamento") or "").strip() for p in cargar_datos_anteriores()
                   if (p.get("departamento") or "").strip() and (p.get("departamento") or "").lower() != "sin departamento"})

def actualizar_postulados_departamento(nombre_departamento, conteo_mapa=None):
    plazas_scrapeadas = obtener_vacantes_por_departamento(nombre_departamento)
    if conteo_mapa is None:
        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception:
            conteo_mapa = {}
    cantidad_esperada = conteo_mapa.get(nombre_departamento)
    with lock_json:
        plazas_bd = cargar_datos_anteriores()
        plazas_bd, ids_nuevas = fusionar_plazas_reconciliando_seguro(
            plazas_bd, plazas_scrapeadas, nombre_departamento, cantidad_esperada)
        guardar_datos_actuales(plazas_bd)
    return len(plazas_scrapeadas), len(ids_nuevas)

def hilo_actualizador_postulados():
    print(f"🧵 Actualizador de postulados (cada {INTERVALO_ACTUALIZACION_POSTULADOS}s).")
    while True:
        if not lock_ejecucion_vigilante.acquire(blocking=False):
            time.sleep(INTERVALO_ACTUALIZACION_POSTULADOS)
            continue
        try:
            with lock_json:
                plazas_bd = cargar_datos_anteriores()
                vigentes, vencidas = limpiar_plazas_vencidas(plazas_bd)
                if vencidas:
                    guardar_datos_actuales(vigentes)
            departamentos = obtener_departamentos_en_json()
            try:
                conteo_mapa = obtener_conteo_marcadores_por_departamento()
            except Exception:
                conteo_mapa = {}
            for depto in departamentos:
                try:
                    actualizar_postulados_departamento(depto, conteo_mapa=conteo_mapa)
                except Exception as e:
                    print(f"   ✘ Error {depto}: {e}")
        except Exception as e:
            print(f"⚠️ Error hilo actualizador: {e}")
        finally:
            lock_ejecucion_vigilante.release()
        time.sleep(INTERVALO_ACTUALIZACION_POSTULADOS)

def hilo_vigilante_automatico():
    print(f"🧵 Vigilante automático (cada {INTERVALO_VIGILANTE_SEGUNDOS}s).")
    time.sleep(5)
    while True:
        if not lock_ejecucion_vigilante.acquire(blocking=False):
            time.sleep(INTERVALO_VIGILANTE_SEGUNDOS)
            continue
        try:
            resultado = ejecutar_vigilante(notificar_siempre=False)
            with lock_estado_vigilante:
                estado_vigilante_automatico["ultima_ejecucion"] = datetime.now(ZONA_COLOMBIA).isoformat()
                estado_vigilante_automatico["ultimo_resultado"] = resultado
                estado_vigilante_automatico["ejecuciones"] += 1
        except Exception as e:
            print(f"⚠️ Error vigilante: {e}")
        finally:
            lock_ejecucion_vigilante.release()
        time.sleep(INTERVALO_VIGILANTE_SEGUNDOS)


def parsear_fecha_cierre(cierre_texto):
    if not cierre_texto:
        return None
    try:
        return datetime.strptime(cierre_texto.strip(), "%d/%m/%Y a las %H:%M").replace(tzinfo=ZONA_COLOMBIA)
    except ValueError:
        return None

def limpiar_plazas_vencidas(plazas):
    ahora = datetime.now(ZONA_COLOMBIA)
    vigentes, vencidas = [], []
    for p in plazas:
        fc = parsear_fecha_cierre(p.get("cierre"))
        if fc and fc <= ahora:
            vencidas.append(p)
        else:
            vigentes.append(p)
    return vigentes, vencidas


# ========== FLUJO PRINCIPAL (OPTIMIZADO) ==========

def ejecutar_vigilante(notificar_siempre=False, chat_id=None, forzar_completo=False):
    """
    Ciclo optimizado:
      1. UNA petición al mapa -> conteo de plazas por departamento.
      2. Comparar con el último conteo guardado.
      3. Escrapear SOLO los departamentos cuyo conteo cambió
         (o todos, si es la primera ejecución o forzar_completo=True).
      4. Notificar por Telegram solo si hay cambios.
    """
    try:
        plazas_bd = cargar_datos_anteriores()
        plazas_antes = [dict(p) for p in plazas_bd]

        # 1. Limpiar vencidas
        plazas_vigentes, plazas_vencidas = limpiar_plazas_vencidas(plazas_bd)
        if plazas_vencidas:
            guardar_datos_actuales(plazas_vigentes)
            plazas_bd = plazas_vigentes

        # 2. Leer mapa UNA vez
        try:
            conteo_mapa_nuevo = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ Error leyendo mapa: {e}")
            return f"Error leyendo mapa: {str(e)[:80]}"

        total_mapa = sum(conteo_mapa_nuevo.values())
        total_mapa_anterior = cargar_total_mapa_anterior()
        conteo_mapa_anterior = cargar_conteo_deptos_anterior()

        # 3. Decidir qué departamentos escrapear
        if forzar_completo or not conteo_mapa_anterior:
            deptos_a_scrapear = set(conteo_mapa_nuevo.keys())
            print(f"🔄 Scrape COMPLETO inicial: {len(deptos_a_scrapear)} deptos")
        else:
            deptos_a_scrapear = set()
            for depto, cnt_nuevo in conteo_mapa_nuevo.items():
                cnt_viejo = conteo_mapa_anterior.get(depto, -1)
                if cnt_nuevo != cnt_viejo:
                    deptos_a_scrapear.add(depto)
            # Departamentos que desaparecieron del mapa
            for depto in conteo_mapa_anterior:
                if depto not in conteo_mapa_nuevo:
                    deptos_a_scrapear.add(depto)
            if deptos_a_scrapear:
                print(f"🔄 Cambios detectados en: {', '.join(sorted(deptos_a_scrapear))}")
            else:
                print("✅ Sin cambios en el mapa. No se escrapea nada.")

        # 4. Escrapear SOLO los departamentos seleccionados
        ids_nuevas_totales = set()
        deptos_ok = set()
        for depto in deptos_a_scrapear:
            try:
                plazas_depto = obtener_vacantes_por_departamento(depto)
                cantidad_esperada = conteo_mapa_nuevo.get(depto)
                plazas_bd, ids_nuevas_depto = fusionar_plazas_reconciliando_seguro(
                    plazas_bd, plazas_depto, depto, cantidad_esperada)
                ids_nuevas_totales |= ids_nuevas_depto
                deptos_ok.add(depto)
            except Exception as e:
                print(f"⚠️ Error scraping {depto} (se reintentará el próximo ciclo): {e}")

        # 5. Guardar datos si hubo cambios
        if deptos_ok:
            guardar_datos_actuales(plazas_bd)
            guardar_ultima_actualizacion_completa(datetime.now(ZONA_COLOMBIA))

        # 6. Actualizar el conteo guardado
        #    - Los deptos que escrapeamos OK: guardamos su conteo NUEVO.
        #    - Los que fallaron: dejamos su conteo VIEJO (para reintentar).
        #    - Deptos que ya no están en el mapa: se eliminan.
        conteo_a_guardar = dict(conteo_mapa_anterior)
        for depto in deptos_ok:
            if depto in conteo_mapa_nuevo:
                conteo_a_guardar[depto] = conteo_mapa_nuevo[depto]
        for depto in list(conteo_a_guardar.keys()):
            if depto not in conteo_mapa_nuevo:
                del conteo_a_guardar[depto]
        if conteo_a_guardar != conteo_mapa_anterior:
            guardar_conteo_deptos(conteo_a_guardar)

        # 7. Detectar cambios y notificar
        cambios = detectar_cambios_completos(plazas_bd, plazas_antes)
        hay_cambios = (cambios["total_nuevas"] > 0 or
                       cambios["total_eliminadas"] > 0 or
                       len(plazas_vencidas) > 0)

        resumen_estado = f"Deptos escrapeados: {len(deptos_ok)}/{len(deptos_a_scrapear)}"

        if hay_cambios or notificar_siempre:
            resumen = construir_resumen_completo(plazas_bd, plazas_antes, total_mapa, cambios, total_mapa_anterior)
            enviar_telegram(resumen, chat_id=chat_id)
            guardar_total_mapa_actual(total_mapa)
            return f"Notificación enviada. {resumen_estado}"
        else:
            if chat_id is not None:
                enviar_telegram("✅ Vigilante ejecutado: sin cambios nuevos.", chat_id=chat_id)
            guardar_total_mapa_actual(total_mapa)
            return f"Sin cambios. {resumen_estado}"

    except Exception as e:
        return f"Error: {str(e)[:100]}"


def construir_resumen_completo(plazas_actuales, plazas_anteriores, total_mapa, cambios, total_mapa_anterior):
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_actuales)
    lineas = ["🚨 <b>¡ACTUALIZACIÓN DE PLAZAS SISTEMA MAESTRO!</b> 🚨", ""]
    dif = total_mapa - total_mapa_anterior if total_mapa_anterior else 0
    if dif > 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} <b>(+{dif})</b> ⬆️")
    elif dif < 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} <b>({dif})</b> ⬇️")
    else:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} ↔️")
    lineas.append(f"🆕 <b>Plazas de hoy:</b> {total_hoy}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {total_ayer}")
    lineas.append("")
    deptos = defaultdict(list)
    for p in plazas_actuales:
        deptos[p["departamento"]].append(p)
    lineas.append("--- <b>TODAS LAS PLAZAS ACTIVAS</b> ---")
    lineas.append("")
    ids_nuevas_set = {n["id"] for n in cambios["nuevas"]}
    for depto in sorted(deptos.keys()):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            label = " 🆕" if p["id"] in ids_nuevas_set else ""
            lineas.append(f"  • {html.escape(abreviar_area(p['area']))} ({html.escape(p['municipio'])} - {html.escape(p['zona_tipo'])}){label} – {p['postulados']} postulados")
        lineas.append("")
    lineas.append("")
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')
    return "\n".join(lineas)


def detectar_cambios_completos(plazas_actuales, plazas_anteriores):
    ant = {p["id"]: p for p in plazas_anteriores}
    act = {p["id"]: p for p in plazas_actuales}
    nuevas, eliminadas, actualizadas = [], [], []
    for pid, p in act.items():
        if pid not in ant:
            nuevas.append(p)
        elif p["postulados"] != ant[pid]["postulados"]:
            actualizadas.append({"id": pid})
    for pid, p in ant.items():
        if pid not in act:
            eliminadas.append(p)
    return {"nuevas": nuevas, "eliminadas": eliminadas, "actualizadas": actualizadas,
            "total_nuevas": len(nuevas), "total_eliminadas": len(eliminadas),
            "total_actualizadas": len(actualizadas)}


def contar_plazas_por_activacion(plazas):
    ahora = datetime.now(ZONA_COLOMBIA)
    hoy, ayer = ahora.date(), (ahora.date() - timedelta(days=1))
    ch, ca = 0, 0
    for p in plazas:
        fc = parsear_fecha_cierre(p.get("cierre"))
        if fc:
            fa = (fc - timedelta(days=1)).date()
            if fa == hoy:
                ch += 1
            elif fa == ayer:
                ca += 1
    return ch, ca


def enviar_telegram(mensaje, chat_id=None):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    destino = chat_id if chat_id is not None else TELEGRAM_CHAT_ID
    for parte in _dividir_mensaje(mensaje, 4000):
        try:
            r = requests.post(url, data={"chat_id": destino, "text": parte, "parse_mode": "HTML"}, timeout=10)
            if r.status_code != 200:
                print(f"⚠️ Telegram: {r.status_code} - {r.text}")
        except Exception as e:
            print(f"⚠️ Telegram: {e}")


def _dividir_mensaje(mensaje, limite):
    lineas = mensaje.split("\n")
    partes, actual = [], ""
    for linea in lineas:
        cand = f"{actual}\n{linea}" if actual else linea
        if len(cand) <= limite:
            actual = cand
            continue
        if actual:
            partes.append(actual)
            actual = ""
        if len(linea) <= limite:
            actual = linea
        else:
            for i in range(0, len(linea), limite):
                partes.append(linea[i:i+limite])
    if actual:
        partes.append(actual)
    return partes if partes else [mensaje[:limite]]


lock_estados_menu = threading.Lock()
estados_menu_chat = {}


def obtener_areas_en_json():
    return sorted({(p.get("area") or "").strip() for p in cargar_datos_anteriores()
                   if (p.get("area") or "").strip() and (p.get("area") or "").lower() != "sin área"})


def _es_comando_menu(texto):
    if not texto:
        return False
    t = texto.strip().replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()
    return t in ("menu", "menú", "/menu", "/menú")


def _es_comando_actualizar(texto):
    if not texto:
        return False
    t = texto.strip().replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()
    return t in ("actualizar", "/actualizar")


def _enviar_menu_principal(chat_id):
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": "menu_principal"}
    enviar_telegram("📋 <b>Menú principal</b>\n\n1. Departamento\n2. Áreas\n\nResponde con el número.", chat_id=chat_id)


def _procesar_seleccion_menu(chat_id, texto):
    with lock_estados_menu:
        estado = estados_menu_chat.get(chat_id)
    if not estado:
        return False
    t = (texto or "").strip()
    if not re.fullmatch(r"\d+", t):
        return False
    sel = int(t)
    tipo = estado["tipo"]
    if tipo == "menu_principal":
        if sel == 1:
            dptos = obtener_departamentos_en_json()
            with lock_estados_menu:
                estados_menu_chat[chat_id] = {"tipo": "departamento_lista", "opciones": dptos}
            enviar_telegram("📍 <b>Elige departamento:</b>\n\n" + "\n".join(f"{i}. {d}" for i, d in enumerate(dptos, 1)), chat_id=chat_id)
        elif sel == 2:
            areas = obtener_areas_en_json()
            with lock_estados_menu:
                estados_menu_chat[chat_id] = {"tipo": "area_lista", "opciones": areas}
            enviar_telegram("📚 <b>Elige área:</b>\n\n" + "\n".join(f"{i}. {a}" for i, a in enumerate(areas, 1)), chat_id=chat_id)
        return True
    if tipo in ("departamento_lista", "area_lista"):
        opciones = estado.get("opciones", [])
        if not (1 <= sel <= len(opciones)):
            enviar_telegram(f"Opción inválida (1-{len(opciones)})", chat_id=chat_id)
            return True
        elegido = opciones[sel - 1]
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        enviar_telegram(f"🔎 Buscando: {elegido}...", chat_id=chat_id)
    return True


def _procesar_comando_actualizar(chat_id):
    if not lock_ejecucion_vigilante.acquire(blocking=False):
        enviar_telegram("⏳ Ya hay una actualización en curso.", chat_id=chat_id)
        return
    try:
        enviar_telegram("🔎 Actualizando (forzado completo), dame un momento...", chat_id=chat_id)
        ejecutar_vigilante(notificar_siempre=True, chat_id=chat_id, forzar_completo=True)
    except Exception as e:
        enviar_telegram(f"⚠️ Error: {str(e)[:200]}", chat_id=chat_id)
    finally:
        lock_ejecucion_vigilante.release()


@app.route("/telegram-webhook", methods=["POST"])
def telegram_webhook():
    if TELEGRAM_WEBHOOK_SECRET:
        if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != TELEGRAM_WEBHOOK_SECRET:
            return {"ok": False}, 403
    update = request.get_json(silent=True) or {}
    msg = update.get("message") or update.get("edited_message") or {}
    texto = msg.get("text", "")
    chat_id = (msg.get("chat") or {}).get("id")
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
    try:
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/setWebhook",
                          data={"url": url_publica}, timeout=10)
        return {"webhook_configurado": url_publica, "respuesta_telegram": r.json()}
    except Exception as e:
        return {"error": str(e)}, 500


@app.route("/check")
def check():
    if not lock_ejecucion_vigilante.acquire(blocking=False):
        return {"resultado": "Ya hay una ejecución en curso."}, 409
    def tarea():
        try:
            ejecutar_vigilante(notificar_siempre=False)
        finally:
            lock_ejecucion_vigilante.release()
    threading.Thread(target=tarea, daemon=True).start()
    return {"resultado": "Tarea iniciada en segundo plano"}, 202


@app.route("/check-force")
def check_force():
    return {"resultado": ejecutar_vigilante(notificar_siempre=True, forzar_completo=True)}


@app.route("/status")
def status():
    with lock_estado_vigilante:
        return {"intervalo_segundos": INTERVALO_VIGILANTE_SEGUNDOS,
                "ultima_ejecucion": estado_vigilante_automatico["ultima_ejecucion"],
                "ultimo_resultado": estado_vigilante_automatico["ultimo_resultado"],
                "ejecuciones_desde_arranque": estado_vigilante_automatico["ejecuciones"]}


@app.route("/")
def home():
    try:
        contenido_raw, _ = github_leer_archivo(ARCHIVO_DATOS)
        contenido = json.loads(contenido_raw) if contenido_raw else "No existe"
    except Exception as e:
        contenido = f"Error leyendo desde GitHub: {e}"
    html_page = """<!DOCTYPE html><html><head><meta charset="UTF-8"><title>Vigilante</title>
    <style>body{font-family:Arial;margin:30px}button{padding:10px 20px;margin:5px;cursor:pointer}
    pre{background:#f4f4f4;padding:15px;border-radius:5px;overflow:auto;max-height:400px}
    .card{border:1px solid #ddd;padding:20px;margin-bottom:20px;border-radius:8px}</style></head>
    <body><h1>🕵️ Vigilante de Vacantes</h1>
    <div class="card"><h2>Acciones</h2>
    <button onclick="fetch('/check').then(r=>r.json()).then(d=>alert(d.resultado))">🚀 Ejecutar (rápido, solo cambios)</button>
    <button onclick="fetch('/check-force').then(r=>r.json()).then(d=>alert(d.resultado))">📢 Forzar completo</button>
    <button onclick="fetch('/limpiar-json',{method:'POST'}).then(r=>r.json()).then(d=>alert(d.mensaje))">🗑️ Limpiar</button>
    </div>
    <div class="card"><h2>JSON (GitHub)</h2><pre>__CONTENIDO_JSON__</pre></div>
    </body></html>"""
    return html_page.replace("__CONTENIDO_JSON__", json.dumps(contenido, indent=2, ensure_ascii=False))


@app.route("/limpiar-json", methods=["POST"])
def limpiar_json():
    msgs = []
    for archivo in (ARCHIVO_DATOS, ARCHIVO_TOTAL_MAPA, ARCHIVO_CONTEO_DEPTOS, ARCHIVO_ULTIMA_ACTUALIZACION):
        try:
            if github_eliminar_archivo(archivo):
                msgs.append(f"{archivo} eliminado.")
            else:
                msgs.append(f"{archivo} no existía.")
        except Exception as e:
            msgs.append(f"Error con {archivo}: {e}")
    return {"mensaje": " ".join(msgs)}, 200


@app.route("/verjson")
def verjson():
    try:
        contenido, _ = github_leer_archivo(ARCHIVO_DATOS)
        if contenido:
            return {"ruta": _gh_path(ARCHIVO_DATOS), "contenido": json.loads(contenido)}
        return {"ruta": _gh_path(ARCHIVO_DATOS), "contenido": "No existe"}
    except Exception as e:
        return {"ruta": _gh_path(ARCHIVO_DATOS), "contenido": f"Error: {e}"}


@app.route("/departamentos")
def obtener_departamentos():
    try:
        r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
        r.raise_for_status()
        coins = re.findall(r'title:\s*[\'"]([^\'"]+)[\'"]', r.text, re.DOTALL)
        contador_mapa = Counter(coins)
        contador_json = defaultdict(int)
        for p in cargar_datos_anteriores():
            d = p.get("departamento", "").strip()
            if d:
                contador_json[d] += 1
        dep = []
        for n, c in contador_mapa.items():
            nd = n.split(" - ")[0].strip()
            dep.append({"nombre": nd, "cantidad": c, "en_json": contador_json.get(nd, 0)})
        dep.sort(key=lambda x: x["cantidad"], reverse=True)
        return {"departamentos": dep, "total": len(coins), "departamentos_unicos": len(dep)}
    except Exception as e:
        return {"error": str(e)}, 500


@app.route("/agregar-departamento", methods=["POST"])
def agregar_departamento():
    try:
        data = request.get_json()
        nombre = data["departamento"].strip()
        plazas = obtener_vacantes_por_departamento(nombre)
        try:
            conteo = obtener_conteo_marcadores_por_departamento()
        except Exception:
            conteo = {}
        plazas_bd = cargar_datos_anteriores()
        fusionadas, nuevas = fusionar_plazas_reconciliando_seguro(
            plazas_bd, plazas, nombre, conteo.get(nombre))
        guardar_datos_actuales(fusionadas)
        return {"mensaje": f"✅ {len(plazas)} plazas de {nombre}",
                "plazas_encontradas": len(plazas),
                "total_plazas_en_json": len(fusionadas),
                "plazas_nuevas": len(nuevas)}
    except Exception as e:
        return {"error": str(e)}, 500


@app.route("/limpiar-vencidas", methods=["POST"])
def limpiar_vencidas():
    plazas = cargar_datos_anteriores()
    vigentes, vencidas = limpiar_plazas_vencidas(plazas)
    if vencidas:
        guardar_datos_actuales(vigentes)
    return {"mensaje": f"Se eliminaron {len(vencidas)} vencidas.", "eliminadas": len(vencidas),
            "restantes": len(vigentes)}, 200


threading.Thread(target=hilo_actualizador_postulados, daemon=True).start()
threading.Thread(target=hilo_vigilante_automatico, daemon=True).start()


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
