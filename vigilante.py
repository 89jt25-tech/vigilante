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
ARCHIVO_TOTAL_MAPA = "total_mapa.json"  # Nuevo archivo para guardar el total del mapa
ZONA_COLOMBIA = ZoneInfo("America/Bogota")

HEADERS_AJAX = {
    "accept": "application/xml, text/xml, */*; q=0.01",
    "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
    "faces-request": "partial/ajax",
    "x-requested-with": "XMLHttpRequest",
    "User-Agent": "Mozilla/5.0",
}

# ========== MAPEO DE DEPARTAMENTOS ==========
DEPARTAMENTOS_CODIGOS = {
    "amazonas": "91",         #confirmado
    "antioquia": "05",        #confirmado
    "arauca": "81",
    "atlántico": "08",
    "bogotá": "11",
    "bogotá d.c": "11",
    "bolívar": "13",
    "boyacá": "15",
    "caldas": "17",
    "caquetá": "18",
    "casanare": "85",
    "cauca": "19",
    "cesar": "20",
    "chocó": "27",
    "córdoba": "23",
    "cundinamarca": "25",
    "guainía": "94",
    "guaviare": "95",
    "huila": "41",
    "la guajira": "44",
    "magdalena": "47",
    "meta": "50",
    "nariño": "52",
    "norte de santander": "54", #confirmado
    "putumayo": "86",
    "quindío": "63",          #confirmado
    "risaralda": "66",
    "san andrés": "88",
    "santander": "68",           #confirmado
    "sucre": "70",
    "tolima": "73",
    "valle del cauca": "76",  #confirmado
    "vaupés": "97",
    "vichada": "99",
}

# ========== ABREVIATURAS DE ÁREAS ==========
AREA_ABREVIATURAS = {
    # Caso especial (sin asignación)
    "sin asignación directa": "Sin Asignación",

    # Ciencias
    "ciencias económicas y políticas": "C. Económicas",
    "ciencias naturales física": "C. Naturales - Física",
    "ciencias naturales química": "C. Naturales - Química",
    "ciencias naturales y educación ambiental": "C. Naturales",
    "ciencias sociales": "C. Sociales",

    # Educación artística
    "educación artística - artes escénicas": "Artes Escénicas",
    "educación artística - artes plásticas": "Artes Plásticas",
    "educación artística – danzas": "Danzas",
    "educación artística – música": "Música",

    # Educación artística (programa PTA)
    "educación artística - danzas (programa pta)": "Danzas - PTA",
    "educación artística - literatura (programa pta)": "Literatura - PTA",
    "educación artística - música (programa pta)": "Música - PTA",

    # Otras áreas
    "educación ética y en valores": "Ética y Valores",
    "educación física, recreación y deporte": "Ed. Física",
    "educación religiosa": "Religión",
    "filosofía": "Filosofía",
    "humanidades y lengua castellana": "Hum. y Len. Castellana",
    "idioma extranjero inglés": "Inglés",
    "matemáticas": "Matemáticas",
    "tecnología e informática": "Tecno-Infor",

    # Áreas de apoyo y niveles educativos
    "áreas de apoyo para educación especial": "Apoyo Ed. Especial",
    "orientadores": "Orientadores",
    "preescolar": "Preescolar",
    "primaria": "Primaria",
}

def abreviar_area(area):
    """
    Devuelve la versión corta de un nombre de área según el diccionario.
    Si no está en el diccionario, devuelve el nombre original.
    """
    if not area:
        return "Sin área"
    area_lower = area.lower().strip()
    return AREA_ABREVIATURAS.get(area_lower, area)


MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6

# ========== HILO DE ACTUALIZACIÓN DE POSTULADOS EN SEGUNDO PLANO ==========
INTERVALO_ACTUALIZACION_POSTULADOS = int(os.environ.get("INTERVALO_ACTUALIZACION_POSTULADOS", 600))

# ========== HILO VIGILANTE AUTOMÁTICO (reemplaza al Cron Job externo) ==========
# Antes esto dependía de un Cron Job de Render pegándole a /check cada minuto.
# Si ese cron se desconfigura, cambia de URL, o el plan no lo soporta, dejas
# de recibir notificaciones automáticas sin enterarte. Este hilo corre DENTRO
# del propio proceso, así que mientras la app esté viva, se ejecuta solo.
INTERVALO_VIGILANTE_SEGUNDOS = int(os.environ.get("INTERVALO_VIGILANTE_SEGUNDOS", 60))

# Guarda info del último chequeo automático, útil para /status.
estado_vigilante_automatico = {
    "ultima_ejecucion": None,
    "ultimo_resultado": None,
    "ejecuciones": 0,
}
lock_estado_vigilante = threading.Lock()

lock_json = threading.RLock()

# Nombre del bot (para reconocer menciones tipo "@VigilanteSistemaMaestroBot Actualizar").
TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")

# Token secreto opcional para verificar que las peticiones al webhook realmente
# vienen de Telegram (se configura al registrar el webhook, ver instrucciones
# más abajo). Si no se define, no se valida (no recomendado en producción).
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")

# Evita que dos "Actualizar" simultáneos disparen dos scrapeos completos a la vez.
lock_ejecucion_vigilante = threading.Lock()

# ============================================================
# CARGA / GUARDADO DE DATOS
# ============================================================

def cargar_datos_anteriores():
    with lock_json:
        if os.path.exists(ARCHIVO_DATOS):
            try:
                with open(ARCHIVO_DATOS, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                return []
        return []

def guardar_datos_actuales(plazas):
    with lock_json:
        if plazas:
            with open(ARCHIVO_DATOS, "w", encoding="utf-8") as f:
                json.dump(plazas, f, ensure_ascii=False, indent=2)
        else:
            print("⚠️ Se intentó guardar una lista vacía de plazas. No se sobrescribió el archivo.")

def obtener_total_plazas_mapa():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    coincidencias = re.findall(patron, r.text)
    return len(coincidencias)

def guardar_total_mapa_actual(total_mapa):
    with open(ARCHIVO_TOTAL_MAPA, "w", encoding="utf-8") as f:
        json.dump({"total_mapa": total_mapa}, f, ensure_ascii=False, indent=2)

def cargar_total_mapa_anterior():
    """Carga el total de plazas del mapa guardado anteriormente"""
    if os.path.exists(ARCHIVO_TOTAL_MAPA):
        try:
            with open(ARCHIVO_TOTAL_MAPA, "r", encoding="utf-8") as f:
                data = json.load(f)
                return data.get("total_mapa", 0)
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
    """Extrae HTML y ViewState de una respuesta parcial AJAX de JSF."""
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

def extraer_html_actualizado(xml_texto):
    """Extrae solo el HTML de la tabla de vacantes."""
    try:
        root = ET.fromstring(xml_texto)
    except ET.ParseError:
        return ""
    for update in root.iter("update"):
        if update.get("id") == "form-busqueda:tabla-vacantes":
            return update.text or ""
    return ""

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

        # Extraer zona geográfica (primera)
        zonas = panel.find_all("label", string=re.compile(r"Zona:"))
        zona_geografica = zonas[0].get_text(strip=True).replace("Zona:", "").strip() if zonas else "Sin zona"
        # Extraer zona tipo (segunda, si existe)
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

def expandir_todos_detalles(session, viewstate, html_actual):
    """
    Dado el HTML de la tabla (con posibles detalles contraídos), hace clic en
    todos los enlaces "Ver detalle" secuencialmente y devuelve el HTML final
    con todos los detalles expandidos y el viewstate actualizado.
    """
    soup = BeautifulSoup(html_actual, 'html.parser')
    max_intentos = 50   # seguridad, para evitar bucles infinitos
    intentos = 0

    while intentos < max_intentos:
        # Buscar todos los enlaces con texto "Ver detalle" dentro de div.vacante
        enlaces = soup.select('div.vacante a.ui-commandlink')
        enlaces_ver = [a for a in enlaces if a.get_text(strip=True) == "Ver detalle"]

        if not enlaces_ver:
            break   # ya no hay detalles contraídos

        # Tomar el primer enlace "Ver detalle" (después de expandir uno, la tabla se actualiza)
        enlace = enlaces_ver[0]
        source_id = enlace.get('id')
        if not source_id:
            break

        # Construir datos para la petición AJAX (similar a pedir_pagina_filtrada)
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
            # Incluir otros campos que puedan ser necesarios (filtros, etc.)
            # Se pueden extraer del HTML actual, pero para simplificar usamos los mismos
            # que enviamos en la paginación. Como no los tenemos aquí, podemos dejar
            # solo los esenciales; en la práctica, el servidor a menudo acepta esto.
            # Para mayor robustez, extraemos todos los inputs ocultos del formulario.
        }

        # Extraer inputs ocultos del formulario actual (para mantener estado)
        formulario = soup.find('form', id='form-busqueda')
        if formulario:
            for input_hidden in formulario.find_all('input', type='hidden'):
                name = input_hidden.get('name')
                value = input_hidden.get('value', '')
                if name and name not in data:
                    data[name] = value

        # Enviar la petición
        response = session.post(URL_PAGINA, headers=HEADERS_AJAX, data=data, timeout=30)
        resultado = extraer_actualizaciones(response.text)

        # Actualizar viewstate y HTML
        nuevo_viewstate = resultado.get("viewstate")
        if nuevo_viewstate:
            viewstate = nuevo_viewstate
        nuevo_html = resultado.get("html")
        if nuevo_html:
            html_actual = nuevo_html
        else:
            # Si no se recibió HTML, puede ser que la respuesta no tenga update de la tabla
            # En ese caso, mantenemos el HTML anterior y salimos
            break

        # Reconstruir soup para la siguiente iteración
        soup = BeautifulSoup(html_actual, 'html.parser')
        intentos += 1

    return html_actual, viewstate

def desambiguar_ids(vacantes):
    """Agrega sufijos a IDs duplicados (por plazas gemelas)."""
    conteo_total = Counter(v["id"] for v in vacantes)
    contador_visto = defaultdict(int)
    for v in vacantes:
        id_base = v["id"]
        if conteo_total[id_base] > 1:
            contador_visto[id_base] += 1
            v["id"] = f"{id_base}__{contador_visto[id_base]}"
    return vacantes

def cambiar_filtro_departamento(session, viewstate, codigo_departamento):
    """
    Simula el cambio del combo 'Departamento' del formulario de búsqueda.
    """
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
    """
    Pide una página de resultados YA con el filtro de departamento activo,
    y expande todos los detalles para obtener la información completa.
    """
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

    # Expandir todos los detalles (opción 3)
    try:
        html_expandido, nuevo_viewstate = expandir_todos_detalles(session, nuevo_viewstate, html_frag)
        return html_expandido, nuevo_viewstate
    except Exception as e:
        print(f"⚠️ Error al expandir detalles en página {first//rows + 1}: {e}")
        # En caso de error, devolvemos el HTML original y el viewstate actualizado
        return html_frag, nuevo_viewstate

def obtener_vacantes_por_departamento(nombre_departamento):
    """
    Obtiene TODAS las vacantes de un departamento usando el filtro.
    """
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
    """
    Extrae los nombres de departamento desde los títulos de los marcadores del mapa.
    """
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
    """
    Combina la base de datos persistente con lo que se scrapea.
    """
    bd_por_id = {p["id"]: dict(p) for p in plazas_bd}
    ids_nuevas = set()
    for p in plazas_scrapeadas:
        if p["id"] in bd_por_id:
            bd_por_id[p["id"]].update(p)
        else:
            bd_por_id[p["id"]] = dict(p)
            ids_nuevas.add(p["id"])
    return list(bd_por_id.values()), ids_nuevas

# ========== HILO: REFRESCO DE POSTULADOS POR DEPARTAMENTO ==========

def obtener_departamentos_en_json():
    plazas = cargar_datos_anteriores()
    departamentos = set()
    for p in plazas:
        depto = (p.get("departamento") or "").strip()
        if depto and depto.lower() != "sin departamento":
            departamentos.add(depto)
    return sorted(departamentos)

def fusionar_plazas_reconciliando(plazas_bd, plazas_scrapeadas, departamento):
    """
    Igual que fusionar_plazas, pero además ELIMINA del JSON las plazas de
    `departamento` que estaban guardadas pero ya no aparecieron en el
    scrape actual (se cerraron/removieron antes de su fecha de cierre).
    Solo úsala cuando tengas la garantía de que el scrape trajo TODAS
    las plazas actuales de ese departamento (sin errores a mitad de camino).
    """
    ids_scrapeadas = {p["id"] for p in plazas_scrapeadas}

    # Todo lo que NO es de este departamento se conserva tal cual
    conservadas = [p for p in plazas_bd if p.get("departamento") != departamento]

    # De lo que SÍ es de este departamento, solo mantenemos lo que sigue
    # apareciendo en el scrape actual
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
    """
    Reconcilia (agrega/actualiza/borra) las plazas de un departamento SOLO
    si el scrape parece completo. Si `cantidad_esperada` se provee y el
    scrape trajo MENOS plazas de las esperadas según el mapa, se asume que
    el scrape fue parcial (timeout, error a mitad de página, etc.) y se
    hace solo un merge ADITIVO (nunca se borra nada), para evitar falsos
    "eliminadas" que luego reaparecen como "nuevas" y generan
    notificaciones de Telegram sin que haya cambiado nada de verdad.
    """
    if cantidad_esperada is not None and len(plazas_scrapeadas) < cantidad_esperada:
        print(
            f"⚠️ Scrape incompleto de {departamento}: se obtuvieron "
            f"{len(plazas_scrapeadas)} de {cantidad_esperada} esperadas según el mapa. "
            f"No se reconcilia (no se borra nada), solo se agrega/actualiza."
        )
        bd_por_id = {p["id"]: dict(p) for p in plazas_bd}
        ids_nuevas = set()
        for p in plazas_scrapeadas:
            if p["id"] in bd_por_id:
                bd_por_id[p["id"]].update(p)
            else:
                bd_por_id[p["id"]] = dict(p)
                ids_nuevas.add(p["id"])
        return list(bd_por_id.values()), ids_nuevas

    # Scrape completo (o sin dato de referencia para comparar) -> reconciliar normalmente
    return fusionar_plazas_reconciliando(plazas_bd, plazas_scrapeadas, departamento)

def actualizar_postulados_departamento(nombre_departamento, conteo_mapa=None):
    plazas_scrapeadas = obtener_vacantes_por_departamento(nombre_departamento)

    if conteo_mapa is None:
        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa, se reconcilia sin verificación: {e}")
            conteo_mapa = {}

    cantidad_esperada = conteo_mapa.get(nombre_departamento)

    with lock_json:
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
            # 🆕 Limpieza automática de plazas vencidas en cada ciclo
            with lock_json:
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
                print(f"⚠️ No se pudo obtener conteo del mapa para este ciclo: {e}")
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

def actualizar_postulados_departamento(nombre_departamento):
    plazas_scrapeadas = obtener_vacantes_por_departamento(nombre_departamento)
    with lock_json:
        plazas_bd = cargar_datos_anteriores()
        total_antes = len([p for p in plazas_bd if p.get("departamento") == nombre_departamento])

        plazas_bd, ids_nuevas = fusionar_plazas_reconciliando(
            plazas_bd, plazas_scrapeadas, nombre_departamento
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
        try:
            # 🆕 Limpieza automática de plazas vencidas en cada ciclo
            with lock_json:
                plazas_bd = cargar_datos_anteriores()
                vigentes, vencidas = limpiar_plazas_vencidas(plazas_bd)
                if vencidas:
                    guardar_datos_actuales(vigentes)
                    print(f"🗑️ {len(vencidas)} plaza(s) vencida(s) eliminada(s) automáticamente.")

            departamentos = obtener_departamentos_en_json()
            if departamentos:
                print(f"🔄 Refrescando postulados de {len(departamentos)} departamento(s): {', '.join(departamentos)}")
            for depto in departamentos:
                try:
                    encontradas, nuevas = actualizar_postulados_departamento(depto)
                    print(f"   ✔ {depto}: {encontradas} plazas revisadas, {nuevas} nueva(s)")
                except Exception as e:
                    print(f"   ✘ Error actualizando postulados de '{depto}': {e}")
        except Exception as e:
            print(f"⚠️ Error en hilo actualizador de postulados: {e}")
        time.sleep(INTERVALO_ACTUALIZACION_POSTULADOS)

def hilo_vigilante_automatico():
    """
    Reemplaza al Cron Job externo: corre ejecutar_vigilante() cada
    INTERVALO_VIGILANTE_SEGUNDOS (por defecto 60s) directamente dentro del
    proceso de la app, sin depender de que algo de afuera llame a /check.
    """
    print(f"🧵 Hilo vigilante automático iniciado (cada {INTERVALO_VIGILANTE_SEGUNDOS}s).")
    # Pequeña espera inicial para dejar que la app termine de levantar.
    time.sleep(5)
    while True:
        adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
        if not adquirido:
            # Ya hay una ejecución en curso (p. ej. alguien escribió "Actualizar"
            # justo en este momento); nos saltamos este ciclo.
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

# ========== ELIMINAR PLAZAS VENCIDAS ==========

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
    """
    Cuenta cuántos marcadores (plazas) tiene cada departamento según el
    mapa en vivo. Sirve para verificar si un scrape de un departamento
    trajo TODAS sus plazas antes de confiar en él para borrar "fantasmas".
    """
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
        # 1. Cargar datos anteriores
        plazas_bd = cargar_datos_anteriores()
        total_json_actual = len(plazas_bd)
        plazas_antes = [dict(p) for p in plazas_bd]  # copia profunda real, evita aliasing

        # 2. Limpiar vencidas
        plazas_vigentes, plazas_vencidas = limpiar_plazas_vencidas(plazas_bd)
        if plazas_vencidas:
            guardar_datos_actuales(plazas_vigentes)
            plazas_bd = plazas_vigentes
            total_json_actual = len(plazas_bd)

        # 3. Obtener total del mapa actual (para el resumen) y conteo por depto (para reconciliación segura)
        total_mapa = obtener_total_plazas_mapa()
        total_mapa_anterior = cargar_total_mapa_anterior()

        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa para este ciclo: {e}")
            conteo_mapa = {}

        # 4. SCRAPING COMPLETO SIEMPRE (con reconciliación segura por departamento)
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
        total_json_actual = len(plazas_bd)
        ids_nuevas = ids_nuevas_totales

        # 5. Detectar cambios (nuevas, eliminadas, actualizadas)
        cambios = detectar_cambios_completos(plazas_bd, plazas_antes)

        hay_cambios = (cambios["total_nuevas"] > 0 or
                       cambios["total_eliminadas"] > 0 or
                       # cambios["total_actualizadas"] > 0 or
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
            mensaje_sin_cambios = "✅ Vigilante ejecutado: no hay cambios nuevos respecto a la última revisión."
            if chat_id is not None:
                enviar_telegram(mensaje_sin_cambios, chat_id=chat_id)
            guardar_total_mapa_actual(total_mapa)
            return "Sin cambios notificables."

    except Exception as e:
        #enviar_telegram(f"⚠️ Error en vigilante: {str(e)[:200]}", chat_id=chat_id)
        return f"Error: {str(e)[:100]}"

ARCHIVO_ULTIMA_ACTUALIZACION = "ultima_actualizacion_completa.json"

def guardar_ultima_actualizacion_completa(fecha):
    with open(ARCHIVO_ULTIMA_ACTUALIZACION, "w", encoding="utf-8") as f:
        json.dump({"ultima": fecha.isoformat()}, f)

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
    """
    Construye el mensaje para Telegram incluyendo eliminadas.
    """
    total_hoy, total_ayer = contar_plazas_por_activacion(plazas_actuales)

    lineas = []
    lineas.append("🚨 <b>¡ACTUALIZACIÓN DE PLAZAS SISTEMA MAESTRO!</b> 🚨")
    lineas.append("")

    # Totales
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

   
    # Todas las plazas activas (agrupadas por departamento)
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
            # Indicar si es nueva (aunque ya esté en la sección de cambios, lo ponemos aquí también)
            es_nueva = p["id"] in [n["id"] for n in cambios["nuevas"]]
            label = " 🆕" if es_nueva else ""
            lineas.append(f"  • {area_esc} ({municipio_esc} - {zona_esc}){label} – {p['postulados']} postulados")
        lineas.append("")

    lineas.append("")
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')

    return "\n".join(lineas)


def detectar_cambios_completos(plazas_actuales, plazas_anteriores):
    """
    Compara dos listas de plazas y detecta:
    - nuevas: plazas que no estaban en la versión anterior.
    - eliminadas: plazas que estaban en la anterior pero no en la actual.
    - actualizadas: plazas cuyo postulados cambiaron.
    """
    anteriores_por_id = {p["id"]: p for p in plazas_anteriores}
    actuales_por_id = {p["id"]: p for p in plazas_actuales}

    nuevas = []
    eliminadas = []
    actualizadas = []

    # Detectar nuevas y actualizadas
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

    # Detectar eliminadas
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
    """
    Devuelve una lista con los nombres de los departamentos que tienen
    plazas en el mapa pero no están completas en el JSON.
    """
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

def detectar_cambios(plazas_actuales, plazas_anteriores):
    """
    Compara dos listas de plazas y detecta:
    - nuevas: plazas que no estaban en la versión anterior.
    - actualizadas: plazas cuyo postulados cambiaron.
    - sin_cambios: plazas que no cambiaron.
    """
    anteriores_por_id = {p["id"]: p for p in plazas_anteriores}
    actuales_por_id = {p["id"]: p for p in plazas_actuales}

    nuevas = []
    actualizadas = []
    sin_cambios = []

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
            else:
                sin_cambios.append(p_actual)

    return {
        "nuevas": nuevas,
        "actualizadas": actualizadas,
        "sin_cambios": sin_cambios,
        "total_nuevas": len(nuevas),
        "total_actualizadas": len(actualizadas)
    }

def contar_plazas_por_activacion(plazas):
    """
    Recorre la lista de plazas y cuenta cuántas tienen su fecha de activación
    (cierre - 24h) en el día de hoy y en el día de ayer (zona horaria Colombia).
    Retorna (hoy, ayer).
    """
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

def construir_resumen(plazas_bd, plazas_scrapeadas, total_mapa, ids_nuevas=None, total_mapa_anterior=None):
    """
    Construye el mensaje para Telegram.
    """
    ids_nuevas = ids_nuevas or set()

    total_hoy_json, total_ayer_calculado = contar_plazas_por_activacion(plazas_bd)

    deptos = defaultdict(list)
    for p in plazas_bd:
        deptos[p["departamento"]].append(p)

    lineas = []
    lineas.append("🚨 <b>¡Plazas Sistema Maestro!</b> 🚨")
    lineas.append("")

    if total_mapa_anterior is not None:
        diferencia = total_mapa - total_mapa_anterior
        if diferencia > 0:
            lineas.append(f"🌎 <b>Total plazas activas:</b> {total_mapa} <b>(+{diferencia})</b> ⬆️")
        elif diferencia < 0:
            lineas.append(f"🌎 <b>Total plazas activas:</b> {total_mapa} <b>({diferencia})</b> ⬇️")
        else:
            lineas.append(f"🌎 <b>Total plazas activas:</b> {total_mapa} ↔️")
    else:
        lineas.append(f"🌎 <b>Total plazas activas:</b> {total_mapa}")

    lineas.append(f"🆕 <b>Plazas de hoy:</b> {total_hoy_json}")
    lineas.append(f"📅 <b>Plazas de ayer:</b> {total_ayer_calculado}")

    lineas.append("")
    lineas.append("--- <b>TODAS LAS PLAZAS</b> ---")
    lineas.append("")

    plazas_anteriores = cargar_datos_anteriores()
    anteriores_por_id = {p["id"]: p for p in plazas_anteriores}

    for depto in sorted(deptos.keys()):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            es_nueva = p["id"] in ids_nuevas

            cambio = None
            if not es_nueva and p["id"] in anteriores_por_id:
                anterior = anteriores_por_id[p["id"]]
                if p["postulados"] != anterior["postulados"]:
                    cambio = (anterior["postulados"], p["postulados"])

            area_esc = html.escape(abreviar_area(p["area"]))
            municipio_esc = html.escape(p["municipio"])
            zona_esc = html.escape(p["zona_tipo"])

            if es_nueva:
                linea = f"  • {area_esc} ({municipio_esc} - {zona_esc}) 🆕 – {p['postulados']} postulados"
            else:
                flecha = ""
                if cambio:
                    if cambio[1] > cambio[0]:
                        flecha = " ↑"
                    elif cambio[1] < cambio[0]:
                        flecha = " ↓"
                linea = f"  • {area_esc} ({municipio_esc}){flecha} – {p['postulados']} postulados"

            lineas.append(linea)
        lineas.append("")

    lineas.append("")
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')

    return "\n".join(lineas)

def enviar_telegram(mensaje, chat_id=None):
    """
    Envía un mensaje a Telegram, dividiéndolo en varias partes si supera
    el límite de 4096 caracteres que impone la API de Telegram, y
    registrando en logs cualquier error HTTP.

    chat_id: chat destino. Si no se especifica, se usa el TELEGRAM_CHAT_ID
    configurado por defecto.
    """
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    LIMITE = 4000
    destino = chat_id if chat_id is not None else TELEGRAM_CHAT_ID

    partes = _dividir_mensaje(mensaje, LIMITE)

    for i, parte in enumerate(partes, start=1):
        datos = {"chat_id": destino, "text": parte, "parse_mode": "HTML"}
        try:
            r = requests.post(url, data=datos, timeout=10)
            if r.status_code != 200:
                print(f"⚠️ Error Telegram (parte {i}/{len(partes)}): {r.status_code} - {r.text}")
        except Exception as e:
            print(f"⚠️ Error Telegram (parte {i}/{len(partes)}): {e}")

def _dividir_mensaje(mensaje, limite):
    """
    Divide un mensaje largo en partes que no superen `limite` caracteres,
    intentando cortar por líneas completas para no romper el HTML a la mitad.
    """
    lineas = mensaje.split("\n")
    partes = []
    actual = ""

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
            actual = ""

    if actual:
        partes.append(actual)

    return partes if partes else [mensaje[:limite]]

# ========== MENÚ INTERACTIVO POR TELEGRAM (Departamento / Áreas) ==========

# Guarda, por chat_id, en qué paso del menú está esa conversación:
# {"tipo": "menu_principal" | "departamento_lista" | "area_lista", "opciones": [...]}
lock_estados_menu = threading.Lock()
estados_menu_chat = {}

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
    """
    Igual que construir_resumen, pero para un subconjunto ya filtrado
    (por departamento o por área). El total mostrado es el del subconjunto,
    no el total general del mapa.
    """
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
    """
    Determina si el texto equivale al comando "Menú" (con las mismas
    tolerancias que _es_comando_actualizar: mayúsculas/minúsculas,
    mención al bot, y forma de comando "/menu").
    """
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
    mensaje = (
        "📋 <b>Menú principal</b>\n\n"
        "1. Departamento\n"
        "2. Áreas\n\n"
        "Responde con el número de la opción."
    )
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
    """
    Si este chat tiene un menú pendiente (menú principal, lista de
    departamentos o lista de áreas) y el texto recibido es un número,
    procesa la selección y responde. Devuelve True si consumió el mensaje
    como parte del flujo del menú; False si no había menú pendiente o el
    texto no era una selección válida (para no interferir con otros
    comandos, como "Actualizar").
    """
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
            enviar_telegram(
                f"Opción inválida. Responde un número entre 1 y {len(opciones)}.",
                chat_id=chat_id,
            )
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

# ========== COMANDO "Actualizar" DESDE TELEGRAM (WEBHOOK) ==========

def _es_comando_actualizar(texto):
    """
    Determina si el texto de un mensaje de Telegram equivale al comando
    "Actualizar", tolerando:
      - Mayúsculas/minúsculas ("actualizar", "ACTUALIZAR", "Actualizar")
      - Mención al bot delante ("@VigilanteSistemaMaestroBot Actualizar")
      - Forma de comando ("/actualizar", "/actualizar@VigilanteSistemaMaestroBot")
    """
    if not texto:
        return False

    texto = texto.strip()

    mencion = f"@{TELEGRAM_BOT_USERNAME}"
    texto_sin_mencion = texto.replace(mencion, "").strip()

    candidato = texto_sin_mencion.lower()

    if candidato in ("actualizar", "/actualizar"):
        return True

    return False

def _procesar_comando_actualizar(chat_id):
    """
    Se ejecuta en un hilo aparte (para no bloquear la respuesta al webhook
    de Telegram, que espera un 200 OK rápido). Corre ejecutar_vigilante()
    forzando notificación y respondiendo al chat que escribió "Actualizar".
    """
    adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
    if not adquirido:
        enviar_telegram(
            "⏳ Ya hay una actualización en curso. Te aviso cuando termine esa.",
            chat_id=chat_id,
        )
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
    """
    Endpoint que Telegram llama cada vez que hay un mensaje nuevo en un chat
    donde está el bot (una vez configurado el webhook, ver instrucciones al
    final del archivo).

    Si el texto del mensaje es "Actualizar" (con las variantes toleradas en
    _es_comando_actualizar) -- venga de CUALQUIER usuario/chat -- dispara
    ejecutar_vigilante() en un hilo aparte y responde de inmediato 200 OK a
    Telegram para no generar timeouts.
    """
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
    """
    Endpoint de conveniencia: registra la URL pública de este servicio como
    webhook de Telegram, para no tener que llamar la API a mano con curl.
    Visítala UNA VEZ desde el navegador después de desplegar
    (ej: https://tu-app.onrender.com/set-webhook).
    """
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
    # 1. Intentar adquirir el lock SIN bloquear (igual que en tu código original)
    adquirido = lock_ejecucion_vigilante.acquire(blocking=False)
    if not adquirido:
        return {"resultado": "Ya hay una ejecución en curso, se omitió este chequeo."}, 409  # Conflict

    # 2. Lanzar un hilo que ejecute la tarea y, al terminar, libere el lock
    def tarea_con_lock():
        try:
            ejecutar_vigilante(notificar_siempre=False)
        except Exception as e:
            print(f"Error en hilo de /check: {e}")
        finally:
            lock_ejecucion_vigilante.release()

    threading.Thread(target=tarea_con_lock, daemon=True).start()

    # 3. Responder inmediatamente para que cron-job.org no haga timeout
    return {"resultado": "Tarea iniciada en segundo plano"}, 202

@app.route("/check-force")
def check_force():
    resultado = ejecutar_vigilante(notificar_siempre=True)
    return {"resultado": resultado}

@app.route("/status")
def status():
    """
    Endpoint rápido para confirmar que el hilo vigilante automático sigue
    vivo y ver cuándo fue su última ejecución, sin tener que mirar logs.
    """
    with lock_estado_vigilante:
        return {
            "intervalo_segundos": INTERVALO_VIGILANTE_SEGUNDOS,
            "ultima_ejecucion": estado_vigilante_automatico["ultima_ejecucion"],
            "ultimo_resultado": estado_vigilante_automatico["ultimo_resultado"],
            "ejecuciones_desde_arranque": estado_vigilante_automatico["ejecuciones"],
        }

@app.route("/")
def home():
    ruta = os.path.abspath(ARCHIVO_DATOS)
    contenido = "No existe"
    if os.path.exists(ruta):
        with open(ruta, "r", encoding="utf-8") as f:
            contenido = json.load(f)

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
            <pre>__CONTENIDO_JSON__</pre>
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
                fetch('/check')
                    .then(response => response.json())
                    .then(data => {
                        document.getElementById('resultado').innerHTML = '✅ ' + data.resultado;
                    })
                    .catch(error => {
                        document.getElementById('resultado').innerHTML = '❌ Error: ' + error;
                    });
            }

            function ejecutarCheckForce() {
                document.getElementById('resultado').innerHTML = '⏳ Enviando notificación...';
                fetch('/check-force')
                    .then(response => response.json())
                    .then(data => {
                        document.getElementById('resultado').innerHTML = '✅ ' + data.resultado;
                    })
                    .catch(error => {
                        document.getElementById('resultado').innerHTML = '❌ Error: ' + error;
                    });
            }

            function verDepartamentos() {
                const card = document.getElementById('departamentos-card');
                const content = document.getElementById('departamentos-content');

                card.style.display = 'block';
                content.innerHTML = '⏳ Cargando departamentos...';

                fetch('/departamentos')
                    .then(response => response.json())
                    .then(data => {
                        if (data.error) {
                            content.innerHTML = `❌ ${data.error}`;
                            return;
                        }

                        let html = `
                            <p><b>Total plazas (mapa):</b> ${data.total}</p>
                            <p><b>Departamentos únicos:</b> ${data.departamentos_unicos}</p>
                            <br>
                            <table>
                                <thead>
                                    <tr>
                                        <th>Departamento</th>
                                        <th style="text-align: center;">Cantidad de plazas</th>
                                        <th style="text-align: center;">Acción</th>
                                    </tr>
                                </thead>
                                <tbody>
                        `;

                        data.departamentos.forEach((d, index) => {
                            const bgColor = index % 2 === 0 ? '#ffffff' : '#f9f9f9';
                            const completo = d.en_json >= d.cantidad;
                            const btnClass = completo ? 'btn-success' : 'btn-warning';
                            const btnText = completo ? '✅ Completo' : `📥 Agregar ${d.cantidad} plazas`;
                            const disabled = completo ? 'disabled' : '';
                            html += `
                                <tr style="background-color: ${bgColor};">
                                    <td><b>${d.nombre}</b></td>
                                    <td style="text-align: center;"><b>${d.cantidad}</b> (JSON: ${d.en_json})</td>
                                    <td style="text-align: center;">
                                        <button class="btn-departamento ${btnClass}" onclick="agregarDepartamento('${d.nombre}')" ${disabled}>
                                            ${btnText}
                                        </button>
                                    </td>
                                </tr>
                            `;
                        });

                        html += `
                                    </tbody>
                                </table>
                                <br>
                                <button onclick="document.getElementById('departamentos-card').style.display='none'">Cerrar</button>
                            `;

                        content.innerHTML = html;
                    })
                    .catch(error => {
                        content.innerHTML = `❌ Error al cargar: ${error}`;
                    });
            }

            function actualizarContenidoJSON() {
                fetch('/verjson', { cache: 'no-store' })   // 👈 evita respuesta cacheada
                    .then(response => response.json())
                    .then(data => {
                        const pre = document.querySelector('pre');
                        if (pre) {
                            pre.textContent = JSON.stringify(data.contenido, null, 2);
                        }
                    })
                    .catch(error => console.error('Error al actualizar JSON:', error));
            }

            // Refresco automático del contenido del JSON en pantalla.
            // El vigilante corre en el servidor cada minuto y puede cambiar los
            // datos (plazas nuevas, postulados actualizados, plazas
            // vencidas eliminadas) sin que la página lo sepa. Este
            // intervalo mantiene la vista sincronizada mientras esté abierta,
            // sin necesidad de recargar manualmente.
            const INTERVALO_REFRESCO_MS = 30000; // 30 segundos
            setInterval(actualizarContenidoJSON, INTERVALO_REFRESCO_MS);

            function agregarDepartamento(departamento) {
                const confirmar = confirm(`¿Seguro que quieres agregar todas las plazas de "${departamento}" al JSON?`);
                if (!confirmar) return;

                const resultadoDiv = document.getElementById('resultado');
                resultadoDiv.innerHTML = `⏳ Agregando plazas de ${departamento}...`;

                fetch('/agregar-departamento', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ departamento: departamento })
                })
                .then(response => response.json())
                .then(data => {
                    if (data.error) {
                        resultadoDiv.innerHTML = `❌ ${data.error}`;
                        alert(`❌ Error: ${data.error}`);
                    } else {
                        resultadoDiv.innerHTML = `✅ ${data.mensaje} (Total en JSON: ${data.total_plazas_en_json})`;
                        alert(`✅ ${data.mensaje}\\nEncontradas: ${data.plazas_encontradas}\\nNuevas agregadas: ${data.plazas_nuevas}`);
                        verDepartamentos();
                        actualizarContenidoJSON();
                    }
                })
                .catch(error => {
                    resultadoDiv.innerHTML = `❌ Error al agregar: ${error}`;
                    alert(`❌ Error: ${error}`);
                });
            }

            function limpiarJSON() {
                if (confirm('⚠️ ¿Estás seguro de que quieres ELIMINAR TODOS los datos guardados? Esta acción no se puede deshacer.')) {
                    const resultadoDiv = document.getElementById('resultado');
                    resultadoDiv.innerHTML = '⏳ Eliminando datos...';

                    fetch('/limpiar-json', { method: 'POST' })
                        .then(response => response.json())
                        .then(data => {
                            if (data.error) {
                                resultadoDiv.innerHTML = '❌ ' + data.error;
                                alert('❌ Error: ' + data.error);
                            } else {
                                resultadoDiv.innerHTML = '✅ ' + data.mensaje;
                                alert('✅ ' + data.mensaje);
                                location.reload();
                            }
                        })
                        .catch(error => {
                            resultadoDiv.innerHTML = '❌ Error al limpiar: ' + error;
                            alert('❌ Error: ' + error);
                        });
                }
            }

            function agregarTodosLosDepartamentos() {
                const confirmar = confirm('⚠️ ¿Seguro que quieres agregar todas las plazas de TODOS los departamentos pendientes?');
                if (!confirmar) return;

                const btn = document.querySelector('button[onclick="agregarTodosLosDepartamentos()"]');
                btn.disabled = true;
                btn.textContent = '⏳ Procesando...';

                const resultadoDiv = document.getElementById('resultado');
                resultadoDiv.innerHTML = '⏳ Obteniendo lista de departamentos...';

                fetch('/departamentos')
                    .then(response => response.json())
                    .then(data => {
                        if (data.error) {
                            resultadoDiv.innerHTML = `❌ Error al obtener departamentos: ${data.error}`;
                            alert('❌ Error: ' + data.error);
                            btn.disabled = false;
                            btn.textContent = '🚀 Agregar todos los departamentos pendientes';
                            return;
                        }

                        const pendientes = data.departamentos.filter(d => d.en_json < d.cantidad);

                        if (pendientes.length === 0) {
                            resultadoDiv.innerHTML = '✅ Todos los departamentos ya están completos. ¡No hay nada que agregar!';
                            alert('✅ Todos los departamentos ya están completos.');
                            btn.disabled = false;
                            btn.textContent = '🚀 Agregar todos los departamentos pendientes';
                            return;
                        }

                        resultadoDiv.innerHTML = `⏳ Agregando plazas de ${pendientes.length} departamento(s) pendientes... (0/${pendientes.length})`;

                        let procesados = 0;
                        let totalAgregados = 0;
                        let errores = [];

                        function procesarSiguiente() {
                            if (procesados >= pendientes.length) {
                                const mensaje = `✅ Proceso completado. Se agregaron plazas de ${totalAgregados} departamento(s). ${errores.length > 0 ? 'Hubo ' + errores.length + ' error(es).' : ''}`;
                                resultadoDiv.innerHTML = mensaje;
                                alert(mensaje);
                                verDepartamentos();
                                actualizarContenidoJSON();
                                btn.disabled = false;
                                btn.textContent = '🚀 Agregar todos los departamentos pendientes';
                                return;
                            }

                            const depto = pendientes[procesados];
                            const nombre = depto.nombre;
                            resultadoDiv.innerHTML = `⏳ Agregando plazas de ${nombre}... (${procesados + 1}/${pendientes.length})`;

                            fetch('/agregar-departamento', {
                                method: 'POST',
                                headers: { 'Content-Type': 'application/json' },
                                body: JSON.stringify({ departamento: nombre })
                            })
                            .then(response => response.json())
                            .then(data => {
                                if (data.error) {
                                    errores.push(`❌ ${nombre}: ${data.error}`);
                                } else {
                                    totalAgregados++;
                                }
                                procesados++;
                                procesarSiguiente();
                            })
                            .catch(error => {
                                errores.push(`❌ ${nombre}: Error de red: ${error.message}`);
                                procesados++;
                                procesarSiguiente();
                            });
                        }

                        procesarSiguiente();

                    })
                    .catch(error => {
                        resultadoDiv.innerHTML = `❌ Error al obtener departamentos: ${error}`;
                        alert('❌ Error: ' + error);
                        btn.disabled = false;
                        btn.textContent = '🚀 Agregar todos los departamentos pendientes';
                    });
            }

            function limpiarVencidas() {
                if (!confirm('⚠️ ¿Seguro que quieres eliminar todas las plazas cuya fecha de cierre ya pasó?')) return;

                const resultadoDiv = document.getElementById('resultado');
                resultadoDiv.innerHTML = '⏳ Eliminando plazas vencidas...';

                fetch('/limpiar-vencidas', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' }
                })
                .then(response => response.json())
                .then(data => {
                    if (data.error) {
                        resultadoDiv.innerHTML = `❌ ${data.error}`;
                        alert(`❌ Error: ${data.error}`);
                    } else {
                        resultadoDiv.innerHTML = `✅ ${data.mensaje} (Restantes: ${data.restantes || 0})`;
                        alert(`✅ ${data.mensaje}`);
                        verDepartamentos();
                        actualizarContenidoJSON();
                    }
                })
                .catch(error => {
                    resultadoDiv.innerHTML = `❌ Error al eliminar: ${error}`;
                    alert(`❌ Error: ${error}`);
                });
            }

            document.getElementById('cargaForm').addEventListener('submit', function(e) {
                e.preventDefault();
                const textarea = this.querySelector('textarea');
                const jsonStr = textarea.value.trim();
                if (!jsonStr) {
                    alert('❌ Por favor pega un JSON.');
                    return;
                }
                try {
                    JSON.parse(jsonStr);
                } catch (err) {
                    alert('❌ El texto no es un JSON válido. Revisa comillas, comas, etc.\\n' + err.message);
                    return;
                }
                fetch('/cargar-json', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: jsonStr
                })
                .then(response => response.json())
                .then(data => {
                    alert('✅ ' + (data.mensaje || data.error));
                    if (data.mensaje) location.reload();
                })
                .catch(error => {
                    alert('❌ Error al comunicarse con el servidor: ' + error);
                });
            });
        </script>
    </body>
    </html>
    """
    html_page = html_page.replace(
        "__CONTENIDO_JSON__",
        json.dumps(contenido, indent=2, ensure_ascii=False)
    )
    return html_page

@app.route("/limpiar-json", methods=["POST"])
def limpiar_json():
    """
    Elimina el contenido del archivo JSON (reinicia la base de datos).
    """
    try:
        if os.path.exists(ARCHIVO_DATOS):
            os.remove(ARCHIVO_DATOS)
            mensaje = "Archivo plazas.json eliminado."
        else:
            mensaje = "El archivo plazas.json ya no existía."

        if os.path.exists(ARCHIVO_TOTAL_MAPA):
            os.remove(ARCHIVO_TOTAL_MAPA)
            mensaje += " Archivo total_mapa.json eliminado."
        else:
            mensaje += " Archivo total_mapa.json ya no existía."

        return {"mensaje": mensaje}, 200
    except Exception as e:
        return {"error": f"Error al limpiar JSON: {str(e)}"}, 500

@app.route("/cargar-json", methods=["POST"])
def cargar_json():
    try:
        raw_data = request.get_data(as_text=True)
        if not raw_data:
            return {"error": "El cuerpo de la solicitud está vacío"}, 400
        data = json.loads(raw_data)
    except json.JSONDecodeError as e:
        return {"error": f"El JSON es inválido: {str(e)}"}, 400
    except Exception as e:
        return {"error": f"Error al leer la solicitud: {str(e)}"}, 400

    if not isinstance(data, list):
        return {"error": "El JSON debe ser una lista de objetos"}, 400

    if not data:
        return {"error": "El JSON está vacío (lista vacía)"}, 400

    guardar_datos_actuales(data)
    try:
        total_mapa = obtener_total_plazas_mapa()
        guardar_total_mapa_actual(total_mapa)
    except Exception as e:
        print(f"Error al obtener total del mapa: {e}")

    return {"mensaje": f"✅ JSON guardado correctamente ({len(data)} plazas)"}

@app.route("/verjson")
def verjson():
    ruta = os.path.abspath(ARCHIVO_DATOS)
    if os.path.exists(ruta):
        with open(ruta, "r", encoding="utf-8") as f:
            contenido = json.load(f)
        return {"ruta": ruta, "contenido": contenido}
    return {"ruta": ruta, "contenido": "Archivo no existe"}

@app.route("/departamentos")
def obtener_departamentos():
    """
    Devuelve la lista de departamentos con plazas:
    - cantidad: plazas en el mapa
    - en_json: plazas ya guardadas en el JSON para ese departamento
    """
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
            if depto:
                contador_json[depto] += 1

        departamentos = []
        for nombre, cantidad_mapa in contador_mapa.items():
            nombre_depto = nombre.split(" - ")[0].strip()
            cantidad_json = contador_json.get(nombre_depto, 0)
            departamentos.append({
                "nombre": nombre_depto,
                "cantidad": cantidad_mapa,
                "en_json": cantidad_json
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
    """
    Agrega todas las vacantes de un departamento al JSON.
    """
    try:
        data = request.get_json()
        if not data or "departamento" not in data:
            return {"error": "Se requiere el nombre del departamento"}, 400

        departamento_nombre = data["departamento"].strip()

        try:
            plazas_departamento = obtener_vacantes_por_departamento(departamento_nombre)
        except ValueError as e:
            return {"error": str(e)}, 400

        if not plazas_departamento:
            return {"error": f"No se encontraron plazas para '{departamento_nombre}'."}, 404

        try:
            conteo_mapa = obtener_conteo_marcadores_por_departamento()
        except Exception as e:
            print(f"⚠️ No se pudo obtener conteo del mapa: {e}")
            conteo_mapa = {}
        cantidad_esperada = conteo_mapa.get(departamento_nombre)

        plazas_bd = cargar_datos_anteriores()
        plazas_fusionadas, ids_nuevas = fusionar_plazas_reconciliando_seguro(
            plazas_bd, plazas_departamento, departamento_nombre, cantidad_esperada
        )
        guardar_datos_actuales(plazas_fusionadas)

        try:
            total_mapa = obtener_total_plazas_mapa()
            guardar_total_mapa_actual(total_mapa)
        except Exception as e:
            print(f"Error al actualizar total_mapa: {e}")

        return {
            "mensaje": f"✅ Se procesaron {len(plazas_departamento)} plazas de '{departamento_nombre}'",
            "plazas_encontradas": len(plazas_departamento),
            "total_plazas_en_json": len(plazas_fusionadas),
            "plazas_nuevas": len(ids_nuevas),
        }

    except Exception as e:
        return {"error": f"Error al agregar departamento: {str(e)}"}, 500

@app.route("/limpiar-vencidas", methods=["POST"])
def limpiar_vencidas():
    try:
        plazas = cargar_datos_anteriores()
        if not plazas:
            return {"mensaje": "No hay plazas en el JSON", "eliminadas": 0}, 200

        vigentes, vencidas = limpiar_plazas_vencidas(plazas)
        if vencidas:
            guardar_datos_actuales(vigentes)
            return {
                "mensaje": f"Se eliminaron {len(vencidas)} plazas vencidas.",
                "eliminadas": len(vencidas),
                "restantes": len(vigentes)
            }, 200
        else:
            return {"mensaje": "No hay plazas vencidas.", "eliminadas": 0}, 200
    except Exception as e:
        return {"error": str(e)}, 500

# Arranca al importar el módulo (no solo dentro de __main__) para que
# también funcione cuando Render lo despliega con Gunicorn (gunicorn app:app).
# ⚠️ Si usas más de 1 worker de Gunicorn, estos hilos arrancan UNA VEZ POR
# WORKER y terminarás scrapeando / notificando el mismo departamento varias
# veces en paralelo. Con Render, usa un solo worker
# (gunicorn app:app --workers 1) o mueve esta tarea a un Background
# Worker/Cron Job aparte.
threading.Thread(target=hilo_actualizador_postulados, daemon=True).start()
threading.Thread(target=hilo_vigilante_automatico, daemon=True).start()

# ============================================================
# CÓMO ACTIVAR EL COMANDO "Actualizar" (WEBHOOK DE TELEGRAM)
# ============================================================
# Telegram necesita saber a qué URL avisarte cada vez que alguien escribe en
# el chat. Esto se configura UNA SOLA VEZ (no en cada arranque de la app),
# llamando a la API de Telegram desde tu navegador, curl, o Postman -- o
# simplemente visitando /set-webhook una vez desplegada la app:
#
#   https://<TU_APP>.onrender.com/set-webhook
#
# Opcional pero recomendado (evita que cualquiera golpee tu endpoint):
# define la variable de entorno TELEGRAM_WEBHOOK_SECRET con un valor
# aleatorio antes de desplegar.
#
# Para que el bot reaccione a "Actualizar" (sin "/") escrito en GRUPOS,
# hay que desactivar su modo privado en @BotFather:
#   /setprivacy -> selecciona el bot -> Disable
# En chats privados 1 a 1 con el bot esto no es necesario.
#
# Para verificar que el webhook quedó bien configurado:
#
#   https://api.telegram.org/bot<TOKEN>/getWebhookInfo
#
# Una vez hecho esto, cualquier persona en el chat puede escribir
# "Actualizar" (o "@VigilanteSistemaMaestroBot Actualizar" en un grupo, o
# "/actualizar") y el bot ejecutará ejecutar_vigilante() y responderá en
# ese mismo chat con el resumen de plazas.
#
# ============================================================
# CHEQUEO AUTOMÁTICO CADA MINUTO (NUEVO)
# ============================================================
# Ya NO depende de un Cron Job externo de Render. El hilo
# hilo_vigilante_automatico() corre dentro del propio proceso y llama a
# ejecutar_vigilante() cada INTERVALO_VIGILANTE_SEGUNDOS (60s por defecto).
# Puedes cambiar ese intervalo con la variable de entorno
# INTERVALO_VIGILANTE_SEGUNDOS sin tocar el código.
#
# Para confirmar que sigue vivo, visita:
#   https://<TU_APP>.onrender.com/status
#
# ⚠️ Si usas el plan gratuito de Render, el servicio se "duerme" tras un
# rato sin recibir peticiones HTTP externas, y este hilo se detiene con él.
# En ese caso sigue necesitando algo externo (p. ej. un ping gratuito de
# UptimeRobot cada 5 min a la URL raíz "/") solo para mantener el proceso
# despierto -- ya no hace falta que ese ping le pegue específicamente a
# /check, porque el hilo interno se encarga de eso mientras el proceso
# esté vivo. Si estás en un plan "always on", no necesitas ningún ping
# externo.
# ============================================================

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
