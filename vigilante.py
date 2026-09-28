from flask import Flask, request
import requests
import os
import re
import json
import html
import threading
import time
import sqlite3
from datetime import datetime, timedelta
from collections import defaultdict, Counter
from bs4 import BeautifulSoup
import xml.etree.ElementTree as ET
from zoneinfo import ZoneInfo

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 10 * 1024 * 1024  # 10 MB

# ============================================================
# CONFIGURACIÓN Y VARIABLES DE ENTORNO
# ============================================================
TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ARCHIVO_DATOS_LEGACY = "plazas.json"
ARCHIVO_TOTAL_MAPA_LEGACY = "total_mapa.json"
ARCHIVO_ULTIMA_ACTUALIZACION = "ultima_actualizacion_completa.json"
DB_FILE = "plazas.db"  # 🔥 Nueva base de datos SQLite

ZONA_COLOMBIA = ZoneInfo("America/Bogota")

HEADERS_AJAX = {
    "accept": "application/xml, text/xml, */*; q=0.01",
    "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
    "faces-request": "partial/ajax",
    "x-requested-with": "XMLHttpRequest",
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
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
    area_lower = area.lower().strip()
    return AREA_ABREVIATURAS.get(area_lower, area)

MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6

# Hilos: SOLO el actualizador de postulados. El vigilante automático
# se eliminó para evitar colisiones con cron-job.org.
INTERVALO_ACTUALIZACION_POSTULADOS = int(os.environ.get("INTERVALO_ACTUALIZACION_POSTULADOS", 600))

estado_vigilante_automatico = {
    "ultima_ejecucion": None,
    "ultimo_resultado": None,
    "ejecuciones": 0,
}
lock_estado_vigilante = threading.Lock()

lock_db = threading.RLock()  # Protege operaciones complejas en la DB

TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")

lock_ejecucion_vigilante = threading.Lock()

# ============================================================
# BASE DE DATOS SQLITE (reemplaza al archivo JSON)
# ============================================================

def init_db():
    """Crea la tabla de plazas si no existe y migra datos del JSON legacy."""
    with sqlite3.connect(DB_FILE, timeout=30) as conn:
        conn.row_factory = sqlite3.Row
        conn.execute('''CREATE TABLE IF NOT EXISTS plazas (
            id TEXT PRIMARY KEY,
            area TEXT,
            secretaria TEXT,
            zona TEXT,
            zona_tipo TEXT,
            departamento TEXT,
            municipio TEXT,
            tipo_priorizacion TEXT,
            cierre TEXT,
            postulados INTEGER,
            cargo TEXT
        )''')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_departamento ON plazas(departamento)')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_area ON plazas(area)')
        conn.commit()

def _migrar_json_a_sqlite():
    """Si existe plazas.json, lo importa a SQLite y lo renombra a .bak."""
    if os.path.exists(ARCHIVO_DATOS_LEGACY):
        try:
            with open(ARCHIVO_DATOS_LEGACY, "r", encoding="utf-8") as f:
                datos = json.load(f)
            if isinstance(datos, list) and datos:
                print(f"📦 Migrando {len(datos)} plazas desde JSON a SQLite...")
                with sqlite3.connect(DB_FILE, timeout=30) as conn:
                    for p in datos:
                        conn.execute('''INSERT OR REPLACE INTO plazas 
                            (id, area, secretaria, zona, zona_tipo, departamento, 
                             municipio, tipo_priorizacion, cierre, postulados, cargo)
                            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                            (p.get("id"), p.get("area"), p.get("secretaria"),
                             p.get("zona"), p.get("zona_tipo"), p.get("departamento"),
                             p.get("municipio"), p.get("tipo_priorizacion"),
                             p.get("cierre"), p.get("postulados", 0), p.get("cargo")))
                    conn.commit()
                os.rename(ARCHIVO_DATOS_LEGACY, ARCHIVO_DATOS_LEGACY + ".bak")
                print("✅ Migración completada. JSON antiguo guardado como .bak")
        except Exception as e:
            print(f"⚠️ Error migrando JSON: {e}")

def cargar_datos_anteriores():
    """Devuelve todas las plazas como lista de diccionarios."""
    with lock_db:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute("SELECT * FROM plazas")
            return [dict(row) for row in cursor.fetchall()]

def guardar_datos_actuales(plazas):
    """Guarda la lista completa de plazas en SQLite (INSERT OR REPLACE)."""
    if not plazas:
        print("⚠️ Lista vacía, no se sobreescribe la base.")
        return
    with lock_db:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            conn.execute("DELETE FROM plazas")  # Reemplazo total de la tabla
            conn.executemany('''INSERT INTO plazas 
                (id, area, secretaria, zona, zona_tipo, departamento, 
                 municipio, tipo_priorizacion, cierre, postulados, cargo)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                [(p.get("id"), p.get("area"), p.get("secretaria"),
                  p.get("zona"), p.get("zona_tipo"), p.get("departamento"),
                  p.get("municipio"), p.get("tipo_priorizacion"),
                  p.get("cierre"), p.get("postulados", 0), p.get("cargo"))
                 for p in plazas])
            conn.commit()

def obtener_total_plazas_mapa():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    coincidencias = re.findall(patron, r.text)
    return len(coincidencias)

def guardar_total_mapa_actual(total_mapa):
    """Guarda en un archivo simple (no requiere SQLite)."""
    try:
        with open("total_mapa.json", "w", encoding="utf-8") as f:
            json.dump({"total_mapa": total_mapa}, f, ensure_ascii=False)
    except Exception as e:
        print(f"⚠️ Error guardando total_mapa: {e}")

def cargar_total_mapa_anterior():
    if os.path.exists("total_mapa.json"):
        try:
            with open("total_mapa.json", "r", encoding="utf-8") as f:
                return json.load(f).get("total_mapa", 0)
        except Exception:
            return 0
    return 0

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
        postulados = int(re.search(r"\d+", postulados_texto).group()) if postulados_texto and re.search(r"\d+", postulados_texto) else 0
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

        vacante = {
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
        }
        vacantes.append(vacante)
    return vacantes

def expandir_todos_detalles(session, viewstate, html_actual, intentos_max=3):
    """Expande todos los 'Ver detalle' con reintentos y delays."""
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

        # 🔥 Reintentos con renovación de ViewState
        exitoso = False
        for intento in range(intentos_max):
            try:
                time.sleep(0.8)  # Delay anti-ban
                response = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
                response.raise_for_status()
                
                # Verificar si el servidor respondió con error de sesión
                if "error" in response.text.lower() or "sesión" in response.text.lower():
                    print("⚠️ Sesión expirada al expandir detalle, renovando ViewState...")
                    nuevo_vs = obtener_viewstate(session)
                    if nuevo_vs:
                        viewstate = nuevo_vs
                        data["javax.faces.ViewState"] = viewstate
                    continue
                
                resultado = extraer_actualizaciones(response.text)
                nuevo_viewstate = resultado.get("viewstate")
                if nuevo_viewstate:
                    viewstate = nuevo_viewstate
                nuevo_html = resultado.get("html")
                if nuevo_html:
                    html_actual = nuevo_html
                exitoso = True
                break
            except Exception as e:
                print(f"⚠️ Error expandiendo detalle (intento {intento+1}): {e}")
                time.sleep(2)
                if intento == intentos_max - 1:
                    return html_actual, viewstate
        
        if not exitoso:
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
    for intento in range(3):
        try:
            time.sleep(1.0)
            r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
            r.raise_for_status()
            resultado = extraer_actualizaciones(r.text)
            nuevo_viewstate = resultado["viewstate"] or viewstate
            return resultado["html"], nuevo_viewstate
        except Exception as e:
            print(f"⚠️ Error cambiando filtro (intento {intento+1}): {e}")
            time.sleep(2)
            if intento == 2:
                raise
    return "", viewstate

def pedir_pagina_filtrada(session, viewstate, first, rows, codigo_departamento):
    """Pide una página con reintentos y renovación automática de ViewState."""
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
    
    for intento in range(3):
        try:
            time.sleep(1.5)  # Delay anti-ban entre páginas
            r = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
            r.raise_for_status()
            
            # Detectar ViewState expirado
            if r.status_code != 200 or "error" in r.text.lower():
                print(f"⚠️ Posible ViewState expirado en página {first//rows + 1}, renovando...")
                nuevo_vs = obtener_viewstate(session)
                if nuevo_vs:
                    viewstate = nuevo_vs
                    data["javax.faces.ViewState"] = viewstate
                continue
            
            resultado = extraer_actualizaciones(r.text)
            nuevo_viewstate = resultado["viewstate"] or viewstate
            html_frag = resultado["html"]

            try:
                html_expandido, nuevo_viewstate = expandir_todos_detalles(session, nuevo_viewstate, html_frag)
                return html_expandido, nuevo_viewstate
            except Exception as e:
                print(f"⚠️ Error al expandir detalles en página {first//rows + 1}: {e}")
                return html_frag, nuevo_viewstate
                
        except requests.exceptions.RequestException as e:
            print(f"⚠️ Error de red en página {first//rows + 1} (intento {intento+1}): {e}")
            if intento == 2:
                raise
            time.sleep(3)
    
    return "", viewstate

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
        if not html_frag:
            break
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
    deptos = set()
    for t in titulos:
        partes = t.split(" - ")
        if partes:
            deptos.add(partes[0].strip())
    return deptos

def fusionar_plazas(plazas_bd, plazas_scrapeadas):
    bd_por_id = {p["id"]: dict(p) for p in plazas_bd}
    ids_nuevas = set()
    for p in plazas_scrapeadas:
        if p["id"] in bd_por_id:
            bd_por_id[p["id"]].update(p)
        else:
            bd_por_id[p["id"]] = dict(p)
            ids_nuevas.add(p["id"])
    return list(bd_por_id.values()), ids_nuevas

def obtener_departamentos_en_json():
    with lock_db:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            cursor = conn.execute("SELECT DISTINCT departamento FROM plazas WHERE departamento != 'Sin departamento' AND departamento != ''")
            return sorted([row[0] for row in cursor.fetchall()])

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
    resultado = conservadas + list(bd_depto_por_id.values())
    return resultado, ids_nuevas

def fusionar_plazas_reconciliando_seguro(plazas_bd, plazas_scrapeadas, departamento, cantidad_esperada=None):
    if cantidad_esperada is not None and len(plazas_scrapeadas) < cantidad_esperada:
        print(f"⚠️ Scrape incompleto de {departamento}: {len(plazas_scrapeadas)} de {cantidad_esperada}. Merge aditivo.")
        return fusionar_plazas(plazas_bd, plazas_scrapeadas)
    return fusionar_plazas_reconciliando(plazas_bd, plazas_scrapeadas, departamento)

def actualizar_postulados_departamento(nombre_departamento, conteo_mapa=None):
    plazas_scrapeadas = obtener_vacantes_por_departamento(nombre_departamento)

    if conteo_mapa is None:
        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            conteo_mapa = {}

    cantidad_esperada = conteo_mapa.get(nombre_departamento)

    with lock_db:
        plazas_bd = cargar_datos_anteriores()
        total_antes = len([p for p in plazas_bd if p.get("departamento") == nombre_departamento])

        plazas_bd, ids_nuevas = fusionar_plazas_reconciliando_seguro(
            plazas_bd, plazas_scrapeadas, nombre_departamento, cantidad_esperada
        )
        guardar_datos_actuales(plazas_bd)

        total_despues = len([p for p in plazas_bd if p.get("departamento") == nombre_departamento])
        eliminadas = total_antes - total_despues + len(ids_nuevas)
        if eliminadas > 0:
            print(f"🗑️ Reconciliación {nombre_departamento}: {eliminadas} plaza(s) fantasma eliminada(s)")

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
            with lock_db:
                plazas_bd = cargar_datos_anteriores()
                vigentes, vencidas = limpiar_plazas_vencidas(plazas_bd)
                if vencidas:
                    guardar_datos_actuales(vigentes)
                    print(f"🗑️ {len(vencidas)} plaza(s) vencida(s) eliminada(s) automáticamente.")

            departamentos = obtener_departamentos_en_json()
            if departamentos:
                print(f"🔄 Refrescando postulados de {len(departamentos)} departamento(s): {', '.join(departamentos)}")

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

# ========== ELIMINAR PLAZAS VENCIDAS ==========

def parsear_fecha_cierre(cierre_texto):
    """Parser de fechas tolerante usando regex para mayor robustez."""
    if not cierre_texto:
        return None
    try:
        match = re.search(r'(\d{1,2})/(\d{1,2})/(\d{4}).*?(\d{1,2}):(\d{2})', cierre_texto.strip())
        if match:
            dia, mes, anio, hora, minuto = match.groups()
            fecha_naive = datetime(int(anio), int(mes), int(dia), int(hora), int(minuto))
            return fecha_naive.replace(tzinfo=ZONA_COLOMBIA)
        return None
    except (ValueError, TypeError):
        return None

def limpiar_plazas_vencidas(plazas):
    ahora = datetime.now(ZONA_COLOMBIA)
    vigentes = []
    vencidas = []
    for p in plazas:
        fecha_cierre = parsear_fecha_cierre(p.get("cierre"))
        if fecha_cierre and fecha_cierre <= ahora:
            vencidas.append(p)
        else:
            vigentes.append(p)
    return vigentes, vencidas

def obtener_conteo_marcadores_por_departamento():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    titulos = re.findall(patron, r.text)
    contador = Counter()
    for t in titulos:
        nombre = t.split(" - ")[0].strip()
        contador[nombre] += 1
    return contador

# ========== FLUJO PRINCIPAL ==========

def ejecutar_vigilante(notificar_siempre=False, chat_id=None):
    try:
        plazas_bd = cargar_datos_anteriores()
        total_json_actual = len(plazas_bd)
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
                total_antes_depto = len([p for p in plazas_bd if p.get("departamento") == depto])

                plazas_bd, ids_nuevas_depto = fusionar_plazas_reconciliando_seguro(
                    plazas_bd, plazas_depto, depto, cantidad_esperada
                )
                ids_nuevas_totales |= ids_nuevas_depto

                total_despues_depto = len([p for p in plazas_bd if p.get("departamento") == depto])
                eliminadas_depto = total_antes_depto - total_despues_depto + len(ids_nuevas_depto)
                if eliminadas_depto > 0:
                    print(f"🗑️ Reconciliación {depto}: {eliminadas_depto} plaza(s) fantasma eliminada(s)")
            except Exception as e:
                print(f"⚠️ Error scraping {depto}: {e}")

        guardar_datos_actuales(plazas_bd)
        guardar_ultima_actualizacion_completa(datetime.now(ZONA_COLOMBIA))
        ids_nuevas = ids_nuevas_totales

        cambios = detectar_cambios_completos(plazas_bd, plazas_antes)

        hay_cambios = (cambios["total_nuevas"] > 0 or
                       cambios["total_eliminadas"] > 0 or
                       len(plazas_vencidas) > 0)

        debe_notificar = hay_cambios or notificar_siempre

        if debe_notificar:
            resumen = construir_resumen_completo(
                plazas_bd,
                plazas_antes,
                total_mapa,
                cambios,
                total_mapa_anterior
            )
            enviar_telegram(resumen, chat_id=chat_id)
            guardar_total_mapa_actual(total_mapa)
            return "Notificación enviada."
        else:
            mensaje_sin_cambios = "✅ Vigilante ejecutado: no hay cambios nuevos."
            if chat_id is not None:
                enviar_telegram(mensaje_sin_cambios, chat_id=chat_id)
            guardar_total_mapa_actual(total_mapa)
            return "Sin cambios notificables."

    except Exception as e:
        print(f"⚠️ Error en ejecutar_vigilante: {e}")
        return f"Error: {str(e)[:100]}"

def guardar_ultima_actualizacion_completa(fecha):
    try:
        with open(ARCHIVO_ULTIMA_ACTUALIZACION, "w", encoding="utf-8") as f:
            json.dump({"ultima": fecha.isoformat()}, f)
    except Exception as e:
        print(f"⚠️ Error guardando última actualización: {e}")

def cargar_ultima_actualizacion_completa():
    if os.path.exists(ARCHIVO_ULTIMA_ACTUALIZACION):
        try:
            with open(ARCHIVO_ULTIMA_ACTUALIZACION, "r", encoding="utf-8") as f:
                data = json.load(f)
                return datetime.fromisoformat(data["ultima"]).replace(tzinfo=ZONA_COLOMBIA)
        except:
            return None
    return None

def construir_resumen_completo(plazas_actuales, plazas_anteriores, total_mapa, cambios, total_mapa_anterior):
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_actuales)

    lineas = []
    lineas.append("🚨 <b>¡ACTUALIZACIÓN DE PLAZAS SISTEMA MAESTRO!</b> 🚨")
    lineas.append("")

    diferencia = total_mapa - total_mapa_anterior if total_mapa_anterior is not None else 0
    if diferencia > 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} <b>(+{diferencia})</b> ⬆️")
    elif diferencia < 0:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {int(total_hoy) + int(total_ayer)} <b>({diferencia})</b> ⬇️")
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
    for depto in sorted(deptos.keys()):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            area_esc = html.escape(abreviar_area(p["area"]))
            municipio_esc = html.escape(p["municipio"])
            zona_esc = html.escape(p["zona_tipo"])
            es_nueva = p["id"] in [n["id"] for n in cambios["nuevas"]]
            label = " 🆕" if es_nueva else ""
            lineas.append(f"  • {area_esc} ({municipio_esc} - {zona_esc}){label} – {p['postulados']} postulados")
        lineas.append("")

    lineas.append("")
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')

    return "\n".join(lineas)

def detectar_cambios_completos(plazas_actuales, plazas_anteriores):
    anteriores_por_id = {p["id"]: p for p in plazas_anteriores}
    actuales_por_id = {p["id"]: p for p in plazas_actuales}

    nuevas = []
    eliminadas = []
    actualizadas = []

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
                    "postulados_actual": p_actual["postulados"]
                })

    for id_plaza, p_anterior in anteriores_por_id.items():
        if id_plaza not in actuales_por_id:
            eliminadas.append(p_anterior)

    return {
        "nuevas": nuevas,
        "eliminadas": eliminadas,
        "actualizadas": actualizadas,
        "total_nuevas": len(nuevas),
        "total_eliminadas": len(eliminadas),
        "total_actualizadas": len(actualizadas)
    }

def obtener_departamentos_pendientes():
    deptos_mapa = obtener_departamentos_del_mapa()
    plazas_json = cargar_datos_anteriores()
    contador_json = defaultdict(int)
    for p in plazas_json:
        depto = p.get("departamento", "").strip()
        if depto:
            contador_json[depto] += 1

    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r'L\.marker\(\[.*?\],\s*\{[^}]*title:\s*[\'"]([^\'"]+)[\'"][^}]*\}\)'
    coincidencias = re.findall(patron, r.text, re.DOTALL)
    if not coincidencias:
        patron2 = r'title:\s*[\'"]([^\'"]+)[\'"]'
        coincidencias = re.findall(patron2, r.text, re.DOTALL)

    contador_mapa = Counter(coincidencias)
    pendientes = []
    for nombre, cantidad_mapa in contador_mapa.items():
        nombre_depto = nombre.split(" - ")[0].strip()
        cantidad_json = contador_json.get(nombre_depto, 0)
        if cantidad_json < cantidad_mapa:
            pendientes.append(nombre_depto)
    return pendientes

def contar_plazas_por_activacion(plazas):
    ahora = datetime.now(ZONA_COLOMBIA)
    hoy = ahora.date()
    ayer = hoy - timedelta(days=1)
    contador_hoy = 0
    contador_ayer = 0

    for p in plazas:
        cierre_texto = p.get("cierre")
        fecha_cierre = parsear_fecha_cierre(cierre_texto)
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

    partes = _dividir_mensaje(mensaje, LIMITE)

    for i, parte in enumerate(partes, start=1):
        datos = {"chat_id": destino, "text": parte, "parse_mode": "HTML"}
        try:
            r = requests.post(url, data=datos, timeout=10)
            if r.status_code != 200:
                print(f"⚠️ Error Telegram (parte {i}/{len(partes)}): {r.status_code} - {r.text[:200]}")
        except Exception as e:
            print(f"⚠️ Error Telegram (parte {i}/{len(partes)}): {e}")

def _dividir_mensaje(mensaje, limite=4000):
    """Divide respetando bloques lógicos para no romper HTML."""
    if len(mensaje) <= limite:
        return [mensaje]
    
    bloques = mensaje.split("\n\n")
    partes = []
    actual = ""
    
    for bloque in bloques:
        if len(bloque) > limite:
            if actual:
                partes.append(actual)
                actual = ""
            lineas = bloque.split("\n")
            for linea in lineas:
                if len(actual) + len(linea) + 1 <= limite:
                    actual += (linea + "\n") if actual else linea
                else:
                    partes.append(actual)
                    actual = linea
            continue
            
        if len(actual) + len(bloque) + 2 <= limite:
            actual += ("\n\n" + bloque) if actual else bloque
        else:
            partes.append(actual)
            actual = bloque
            
    if actual:
        partes.append(actual)
        
    return [p.strip() for p in partes if p.strip()]

# ========== MENÚ INTERACTIVO POR TELEGRAM ==========

lock_estados_menu = threading.Lock()
estados_menu_chat = {}

def obtener_areas_en_json():
    with lock_db:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            cursor = conn.execute("SELECT DISTINCT area FROM plazas WHERE area != 'Sin área' AND area != ''")
            return sorted([row[0] for row in cursor.fetchall()])

def filtrar_plazas_por_departamento(nombre_departamento):
    with lock_db:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute("SELECT * FROM plazas WHERE departamento = ?", (nombre_departamento,))
            return [dict(row) for row in cursor.fetchall()]

def filtrar_plazas_por_area(nombre_area):
    with lock_db:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute("SELECT * FROM plazas WHERE area = ?", (nombre_area,))
            return [dict(row) for row in cursor.fetchall()]

def construir_resumen_filtrado(plazas_filtradas, encabezado=None):
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_filtradas)

    deptos = defaultdict(list)
    for p in plazas_filtradas:
        deptos[p["departamento"]].append(p)

    lineas = []
    lineas.append("🚨 <b>¡Plazas Sistema Maestro!</b> 🚨")
    lineas.append("")
    if encabezado:
        lineas.append(f"🔎 <b>Filtro:</b> {html.escape(encabezado)}")
    lineas.append(f"🌎 <b>Total plazas activas:</b> {len(plazas_filtradas)}")
    lineas.append(f"🆕 <b>Plazas de hoy:</b> {total_hoy}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {total_ayer}")
    lineas.append("")
    lineas.append("--- <b>TODAS LAS PLAZAS</b> ---")
    lineas.append("")

    if not deptos:
        lineas.append("No se encontraron plazas para este filtro.")
    else:
        for depto in sorted(deptos.keys()):
            lineas.append(f"📌 <b>{html.escape(depto)}</b>")
            for p in sorted(deptos[depto], key=lambda x: x["area"]):
                area_esc = html.escape(abreviar_area(p["area"]))
                municipio_esc = html.escape(p["municipio"])
                zona_esc = html.escape(p["zona_tipo"])
                lineas.append(f"  • {area_esc} ({municipio_esc} - {zona_esc}) – {p['postulados']} postulados")
            lineas.append("")

    lineas.append("")
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')

    return "\n".join(lineas)

def _es_comando_menu(texto):
    if not texto:
        return False
    texto = texto.strip()
    mencion = f"@{TELEGRAM_BOT_USERNAME}"
    texto_sin_mencion = texto.replace(mencion, "").strip()
    candidato = texto_sin_mencion.lower()
    return candidato in ("menu", "menú", "/menu", "/menú")

def _enviar_menu_principal(chat_id):
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": "menu_principal"}
    mensaje = "📋 <b>Menú principal</b>\n\n1. Departamento\n2. Áreas\n\nResponde con el número de la opción."
    enviar_telegram(mensaje, chat_id=chat_id)

def _enviar_lista_departamentos(chat_id):
    departamentos = obtener_departamentos_en_json()
    if not departamentos:
        enviar_telegram("No hay departamentos con plazas guardadas todavía.", chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": "departamento_lista", "opciones": departamentos}
    lineas = ["📍 <b>Elige un departamento:</b>", ""]
    for i, nombre in enumerate(departamentos, start=1):
        lineas.append(f"{i}. {nombre}")
    lineas.append("")
    lineas.append("Responde con el número.")
    enviar_telegram("\n".join(lineas), chat_id=chat_id)

def _enviar_lista_areas(chat_id):
    areas = obtener_areas_en_json()
    if not areas:
        enviar_telegram("No hay áreas con plazas guardadas todavía.", chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return
    with lock_estados_menu:
        estados_menu_chat[chat_id] = {"tipo": "area_lista", "opciones": areas}
    lineas = ["📚 <b>Elige un área:</b>", ""]
    for i, nombre in enumerate(areas, start=1):
        lineas.append(f"{i}. {nombre}")
    lineas.append("")
    lineas.append("Responde con el número.")
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
            plazas_filtradas = filtrar_plazas_por_departamento(nombre_elegido)
            mensaje = construir_resumen_filtrado(plazas_filtradas, encabezado=f"Departamento: {nombre_elegido}")
        else:
            plazas_filtradas = filtrar_plazas_por_area(nombre_elegido)
            mensaje = construir_resumen_filtrado(plazas_filtradas, encabezado=f"Área: {nombre_elegido}")

        enviar_telegram(mensaje, chat_id=chat_id)
        with lock_estados_menu:
            estados_menu_chat.pop(chat_id, None)
        return True

    with lock_estados_menu:
        estados_menu_chat.pop(chat_id, None)
    return False

def _es_comando_actualizar(texto):
    if not texto:
        return False
    texto = texto.strip()
    mencion = f"@{TELEGRAM_BOT_USERNAME}"
    texto_sin_mencion = texto.replace(mencion, "").strip()
    candidato = texto_sin_mencion.lower()
    return candidato in ("actualizar", "/actualizar")

def _procesar_comando_actualizar(chat_id):
    adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
    if not adquirido:
        enviar_telegram("⏳ Ya hay una actualización en curso.", chat_id=chat_id)
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
        secreto_recibido = request.headers.get("X-Telegram-Bot-Api-Secret-Token")
        if secreto_recibido != TELEGRAM_WEBHOOK_SECRET:
            return {"ok": False}, 403

    try:
        update = request.get_json(silent=True) or {}
    except Exception:
        update = {}

    mensaje = update.get("message") or update.get("edited_message") or {}
    texto = mensaje.get("text", "")
    chat = mensaje.get("chat", {})
    chat_id = chat.get("id")

    if chat_id is not None and _es_comando_menu(texto):
        _enviar_menu_principal(chat_id)
        return {"ok": True}, 200

    if chat_id is not None and _procesar_seleccion_menu(chat_id, texto):
        return {"ok": True}, 200

    if chat_id is not None and _es_comando_actualizar(texto):
        threading.Thread(
            target=_procesar_comando_actualizar,
            args=(chat_id,),
            daemon=True,
        ).start()

    return {"ok": True}, 200

@app.route("/set-webhook")
def set_webhook():
    url_publica = request.host_url.rstrip("/") + "/telegram-webhook"
    url_api = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/setWebhook"
    try:
        r = requests.post(url_api, data={"url": url_publica}, timeout=10)
        return {"webhook_configurado": url_publica, "respuesta_telegram": r.json()}
    except Exception as e:
        return {"error": str(e)}, 500

# ========== ENDPOINTS DE DIAGNÓSTICO ==========

@app.route("/check")
def check():
    adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
    if not adquirido:
        return {"resultado": "Ya hay una ejecución en curso."}, 409

    def tarea_con_lock():
        try:
            ejecutar_vigilante(notificar_siempre=False)
        except Exception as e:
            print(f"Error en hilo de /check: {e}")
        finally:
            lock_ejecucion_vigilante.release()

    threading.Thread(target=tarea_con_lock, daemon=True).start()
    return {"resultado": "Tarea iniciada en segundo plano"}, 202

@app.route("/check-force")
def check_force():
    resultado = ejecutar_vigilante(notificar_siempre=True)
    return {"resultado": resultado}

@app.route("/status")
def status():
    with lock_estado_vigilante:
        return {
            "intervalo_actualizador": INTERVALO_ACTUALIZACION_POSTULADOS,
            "ultima_ejecucion": estado_vigilante_automatico["ultima_ejecucion"],
            "ultimo_resultado": estado_vigilante_automatico["ultimo_resultado"],
            "ejecuciones_desde_arranque": estado_vigilante_automatico["ejecuciones"],
            "db_type": "sqlite",
        }

@app.route("/")
def home():
    contenido = cargar_datos_anteriores()

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
            .badge { padding: 2px 8px; border-radius: 4px; font-size: 11px; font-weight: bold; }
            .badge-sqlite { background: #28a745; color: white; }
        </style>
    </head>
    <body>
        <h1>🕵️ Vigilante de Vacantes <span class="badge badge-sqlite">SQLite</span></h1>

        <div class="card">
            <h2>Acciones</h2>
            <button class="btn-primary" onclick="ejecutarCheck()">🚀 Ejecutar vigilante (notificar solo si hay cambios)</button>
            <button class="btn-success" onclick="ejecutarCheckForce()">📢 Ejecutar vigilante (SIEMPRE notificar)</button>
            <button class="btn-danger" onclick="limpiarJSON()">🗑️ Limpiar Base de Datos</button>
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
            <h2>Contenido de la Base de Datos (<span id="total-plazas">__TOTAL__</span> plazas)</h2>
            <pre id="json-contenido">__CONTENIDO_JSON__</pre>
        </div>

        <div class="card">
            <h2>Cargar JSON manualmente (reemplaza toda la base)</h2>
            <form id="cargaForm">
                <textarea name="json" rows="10" placeholder="Pega aquí el JSON (debe ser una lista de objetos)"></textarea><br>
                <button type="submit">📤 Cargar JSON</button>
            </form>
        </div>

        <script>
            function ejecutarCheck() {
                fetch('/check').then(r => r.json()).then(d => document.getElementById('resultado').innerHTML = '✅ ' + d.resultado).catch(e => document.getElementById('resultado').innerHTML = '❌ ' + e);
            }
            function ejecutarCheckForce() {
                document.getElementById('resultado').innerHTML = '⏳ Enviando notificación...';
                fetch('/check-force').then(r => r.json()).then(d => document.getElementById('resultado').innerHTML = '✅ ' + d.resultado).catch(e => document.getElementById('resultado').innerHTML = '❌ ' + e);
            }
            function verDepartamentos() {
                const card = document.getElementById('departamentos-card');
                const content = document.getElementById('departamentos-content');
                card.style.display = 'block';
                content.innerHTML = '⏳ Cargando departamentos...';
                fetch('/departamentos').then(r => r.json()).then(data => {
                    if (data.error) { content.innerHTML = `❌ ${data.error}`; return; }
                    let html = `<p><b>Total plazas (mapa):</b> ${data.total}</p><p><b>Departamentos únicos:</b> ${data.departamentos_unicos}</p><br><table><thead><tr><th>Departamento</th><th style="text-align: center;">Cantidad de plazas</th><th style="text-align: center;">Acción</th></tr></thead><tbody>`;
                    data.departamentos.forEach((d, index) => {
                        const completo = d.en_json >= d.cantidad;
                        const btnClass = completo ? 'btn-success' : 'btn-warning';
                        const btnText = completo ? '✅ Completo' : `📥 Agregar ${d.cantidad} plazas`;
                        const disabled = completo ? 'disabled' : '';
                        html += `<tr><td><b>${d.nombre}</b></td><td style="text-align: center;"><b>${d.cantidad}</b> (DB: ${d.en_json})</td><td style="text-align: center;"><button class="btn-departamento ${btnClass}" onclick="agregarDepartamento('${d.nombre}')" ${disabled}>${btnText}</button></td></tr>`;
                    });
                    html += `</tbody></table><br><button onclick="document.getElementById('departamentos-card').style.display='none'">Cerrar</button>`;
                    content.innerHTML = html;
                });
            }
            function actualizarContenidoJSON() {
                fetch('/verjson', { cache: 'no-store' }).then(r => r.json()).then(data => {
                    const pre = document.getElementById('json-contenido');
                    const total = document.getElementById('total-plazas');
                    if (pre) pre.textContent = JSON.stringify(data.contenido, null, 2);
                    if (total && Array.isArray(data.contenido)) total.textContent = data.contenido.length;
                });
            }
            setInterval(actualizarContenidoJSON, 30000);
            function agregarDepartamento(departamento) {
                if (!confirm(`¿Agregar todas las plazas de "${departamento}"?`)) return;
                const resultadoDiv = document.getElementById('resultado');
                resultadoDiv.innerHTML = `⏳ Agregando plazas de ${departamento}...`;
                fetch('/agregar-departamento', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ departamento }) })
                .then(r => r.json()).then(data => {
                    if (data.error) { resultadoDiv.innerHTML = `❌ ${data.error}`; alert(`❌ Error: ${data.error}`); }
                    else { resultadoDiv.innerHTML = `✅ ${data.mensaje} (Total en DB: ${data.total_plazas_en_json})`; verDepartamentos(); actualizarContenidoJSON(); }
                });
            }
            function limpiarJSON() {
                if (!confirm('⚠️ ¿ELIMINAR TODOS los datos? Esta acción no se puede deshacer.')) return;
                fetch('/limpiar-json', { method: 'POST' }).then(r => r.json()).then(data => {
                    alert(data.mensaje || data.error); location.reload();
                });
            }
            function agregarTodosLosDepartamentos() {
                if (!confirm('⚠️ ¿Agregar plazas de TODOS los departamentos pendientes?')) return;
                const btn = document.querySelector('button[onclick="agregarTodosLosDepartamentos()"]');
                btn.disabled = true; btn.textContent = '⏳ Procesando...';
                const resultadoDiv = document.getElementById('resultado');
                fetch('/departamentos').then(r => r.json()).then(data => {
                    const pendientes = data.departamentos.filter(d => d.en_json < d.cantidad);
                    if (pendientes.length === 0) { alert('✅ Todos completos.'); btn.disabled = false; btn.textContent = '🚀 Agregar todos los departamentos pendientes'; return; }
                    let procesados = 0, totalAgregados = 0, errores = [];
                    function procesarSiguiente() {
                        if (procesados >= pendientes.length) { alert(`✅ Completado. ${totalAgregados} deptos. ${errores.length} errores.`); btn.disabled = false; btn.textContent = '🚀 Agregar todos los departamentos pendientes'; verDepartamentos(); actualizarContenidoJSON(); return; }
                        const nombre = pendientes[procesados].nombre;
                        resultadoDiv.innerHTML = `⏳ Procesando ${nombre}... (${procesados + 1}/${pendientes.length})`;
                        fetch('/agregar-departamento', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ departamento: nombre }) })
                        .then(r => r.json()).then(d => { if (!d.error) totalAgregados++; else errores.push(nombre); procesados++; procesarSiguiente(); });
                    }
                    procesarSiguiente();
                });
            }
            function limpiarVencidas() {
                if (!confirm('⚠️ ¿Eliminar plazas vencidas?')) return;
                fetch('/limpiar-vencidas', { method: 'POST' }).then(r => r.json()).then(data => { alert(data.mensaje); verDepartamentos(); actualizarContenidoJSON(); });
            }
            document.getElementById('cargaForm').addEventListener('submit', function(e) {
                e.preventDefault();
                const jsonStr = this.querySelector('textarea').value.trim();
                if (!jsonStr) { alert('❌ Pega un JSON.'); return; }
                try { JSON.parse(jsonStr); } catch (err) { alert('❌ JSON inválido: ' + err.message); return; }
                fetch('/cargar-json', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: jsonStr })
                .then(r => r.json()).then(d => { alert(d.mensaje || d.error); if (d.mensaje) location.reload(); });
            });
        </script>
    </body>
    </html>
    """
    html_page = html_page.replace("__CONTENIDO_JSON__", json.dumps(contenido, indent=2, ensure_ascii=False))
    html_page = html_page.replace("__TOTAL__", str(len(contenido)))
    return html_page

@app.route("/limpiar-json", methods=["POST"])
def limpiar_json():
    try:
        with sqlite3.connect(DB_FILE, timeout=30) as conn:
            conn.execute("DELETE FROM plazas")
            conn.commit()
        return {"mensaje": "✅ Base de datos SQLite vaciada."}, 200
    except Exception as e:
        return {"error": f"Error al limpiar: {str(e)}"}, 500

@app.route("/cargar-json", methods=["POST"])
def cargar_json():
    try:
        raw_data = request.get_data(as_text=True)
        data = json.loads(raw_data)
        if not isinstance(data, list) or not data:
            return {"error": "Debe ser una lista de objetos no vacía"}, 400
        guardar_datos_actuales(data)
        return {"mensaje": f"✅ JSON guardado correctamente ({len(data)} plazas)"}
    except Exception as e:
        return {"error": f"Error: {str(e)}"}, 400

@app.route("/verjson")
def verjson():
    contenido = cargar_datos_anteriores()
    return {"contenido": contenido}

@app.route("/departamentos")
def obtener_departamentos():
    try:
        headers = {"User-Agent": "Mozilla/5.0"}
        response = requests.get(URL_PAGINA, headers=headers, timeout=30)
        response.raise_for_status()
        patron = r'L\.marker\(\[.*?\],\s*\{[^}]*title:\s*[\'"]([^\'"]+)[\'"][^}]*\}\)'
        coincidencias = re.findall(patron, response.text, re.DOTALL)
        if not coincidencias:
            patron2 = r'title:\s*[\'"]([^\'"]+)[\'"]'
            coincidencias = re.findall(patron2, response.text, re.DOTALL)
        if not coincidencias:
            return {"error": "No se encontraron departamentos"}, 404
        contador_mapa = Counter(coincidencias)
        plazas_json = cargar_datos_anteriores()
        contador_json = defaultdict(int)
        for p in plazas_json:
            depto = p.get("departamento", "").strip()
            if depto: contador_json[depto] += 1
        departamentos = []
        for nombre, cantidad_mapa in contador_mapa.items():
            nombre_depto = nombre.split(" - ")[0].strip()
            departamentos.append({"nombre": nombre_depto, "cantidad": cantidad_mapa, "en_json": contador_json.get(nombre_depto, 0)})
        departamentos.sort(key=lambda x: x["cantidad"], reverse=True)
        return {"departamentos": departamentos, "total": len(coincidencias), "departamentos_unicos": len(departamentos)}
    except Exception as e:
        return {"error": f"Error: {str(e)}"}, 500

@app.route("/agregar-departamento", methods=["POST"])
def agregar_departamento():
    try:
        data = request.get_json()
        if not data or "departamento" not in data:
            return {"error": "Se requiere el nombre del departamento"}, 400
        departamento_nombre = data["departamento"].strip()
        plazas_departamento = obtener_vacantes_por_departamento(departamento_nombre)
        if not plazas_departamento:
            return {"error": f"No se encontraron plazas para '{departamento_nombre}'."}, 404
        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except: conteo_mapa = {}
        cantidad_esperada = conteo_mapa.get(departamento_nombre)
        plazas_bd = cargar_datos_anteriores()
        plazas_fusionadas, ids_nuevas = fusionar_plazas_reconciliando_seguro(plazas_bd, plazas_departamento, departamento_nombre, cantidad_esperada)
        guardar_datos_actuales(plazas_fusionadas)
        return {"mensaje": f"✅ Procesadas {len(plazas_departamento)} plazas de '{departamento_nombre}'", "plazas_encontradas": len(plazas_departamento), "total_plazas_en_json": len(plazas_fusionadas), "plazas_nuevas": len(ids_nuevas)}
    except Exception as e:
        return {"error": f"Error: {str(e)}"}, 500

@app.route("/limpiar-vencidas", methods=["POST"])
def limpiar_vencidas():
    try:
        plazas = cargar_datos_anteriores()
        if not plazas: return {"mensaje": "No hay plazas", "eliminadas": 0}, 200
        vigentes, vencidas = limpiar_plazas_vencidas(plazas)
        if vencidas:
            guardar_datos_actuales(vigentes)
            return {"mensaje": f"Eliminadas {len(vencidas)} plazas vencidas.", "eliminadas": len(vencidas), "restantes": len(vigentes)}, 200
        return {"mensaje": "No hay plazas vencidas.", "eliminadas": 0}, 200
    except Exception as e:
        return {"error": str(e)}, 500

# ============================================================
# INICIALIZACIÓN AL ARRANCAR
# ============================================================

# 1. Crear tabla SQLite y migrar datos si existen
init_db()
_migrar_json_a_sqlite()

# 2. Iniciar SOLO el hilo actualizador de postulados.
# El chequeo completo lo maneja cron-job.org apuntando a /check.
threading.Thread(target=hilo_actualizador_postulados, daemon=True).start()

# ============================================================
# INSTRUCCIONES DE DESPLIEGUE
# ============================================================
# 1. En Render, usa este comando de inicio:
#    gunicorn app:app --workers 1 --threads 4
#    (NO uses más de 1 worker o duplicarás el scraping)
#
# 2. En cron-job.org configura un job que apunte cada 5 MINUTOS a:
#    https://<tu-app>.onrender.com/check
#    (5 minutos es ideal para dar tiempo al scraping completo sin saturar)
#
# 3. No es necesario configurar el webhook manualmente si ya lo hiciste.
#    Puedes verificarlo con: https://api.telegram.org/bot<TOKEN>/getWebhookInfo
#
# 4. Para mantener despierto el servicio en el plan gratuito de Render,
#    usa UptimeRobot o similar apuntando a / cada 5 minutos.

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
