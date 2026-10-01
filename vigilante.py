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
app.config['MAX_CONTENT_LENGTH'] = 10 * 1024 * 1024

# ============================================================
# CONFIGURACIÓN
# ============================================================
TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
TELEGRAM_BOT_USERNAME = os.environ.get("TELEGRAM_BOT_USERNAME", "VigilanteSistemaMaestroBot")
TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET")

URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ZONA_COLOMBIA = ZoneInfo("America/Bogota")

# Carpeta de datos. En Render, apunta DATA_DIR a un disco persistente (ej. /var/data)
# o el estado se perderá en cada reinicio/redeploy.
DATA_DIR = os.environ.get("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)
ARCHIVO_DATOS = os.path.join(DATA_DIR, "plazas.json")
ARCHIVO_CONTEOS = os.path.join(DATA_DIR, "conteo_deptos.json")
ARCHIVO_RESUMENES = os.path.join(DATA_DIR, "ultimo_resumen.json")

# Ciclo rápido: 1 GET al mapa + scraping solo de departamentos cuyo conteo cambió.
INTERVALO_RAPIDO = int(os.environ.get("INTERVALO_VIGILANTE_SEGUNDOS", 30))
# Barrido completo (refresca postulados y atrapa cambios que el conteo no ve).
INTERVALO_BARRIDO = int(os.environ.get(
    "INTERVALO_BARRIDO_SEGUNDOS", os.environ.get("INTERVALO_ACTUALIZACION_POSTULADOS", 600)))

MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6

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


def _norm(s):
    return (s or "").strip().lower()


# Locks
lock_json = threading.RLock()          # protege lectura/escritura de plazas.json
lock_notificar = threading.Lock()      # evita avisos duplicados
lock_rapido = threading.Lock()         # un solo ciclo rápido a la vez
lock_barrido = threading.Lock()        # un solo barrido completo a la vez
lock_estado = threading.Lock()
estado = {
    "rapido": {"ultima": None, "resultado": None, "ejecuciones": 0},
    "barrido": {"ultima": None, "resultado": None, "ejecuciones": 0},
}


def _ahora():
    return datetime.now(ZONA_COLOMBIA)


def _marcar_estado(clave, resultado):
    with lock_estado:
        estado[clave]["ultima"] = _ahora().isoformat()
        estado[clave]["resultado"] = resultado
        estado[clave]["ejecuciones"] += 1


# ============================================================
# PERSISTENCIA (escritura atómica)
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


def _leer_json(ruta, defecto):
    if not os.path.exists(ruta):
        return defecto
    try:
        with open(ruta, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"❌ Error leyendo {ruta}: {e}")
        return defecto


def cargar_datos_anteriores():
    with lock_json:
        data = _leer_json(ARCHIVO_DATOS, [])
        return data if isinstance(data, list) else []


def guardar_datos_actuales(plazas):
    with lock_json:
        _escritura_atomica_json(ARCHIVO_DATOS, plazas)


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
        m_post = re.search(r"\d+", postulados_texto) if postulados_texto else None
        postulados = int(m_post.group()) if m_post else 0
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
            for input_hidden in formulario.find_all('input', type='hidden'):
                name = input_hidden.get('name')
                if name and name not in data:
                    data[name] = input_hidden.get('value', '')
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
    conteo_total = Counter(v["id"] for v in vacantes)
    visto = defaultdict(int)
    for v in vacantes:
        base = v["id"]
        if conteo_total[base] > 1:
            visto[base] += 1
            v["id"] = f"{base}__{visto[base]}"
    return vacantes


def _campos_filtro(codigo_departamento, rows):
    return {
        "form-busqueda": "form-busqueda",
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


def cambiar_filtro_departamento(session, viewstate, codigo_departamento):
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:idInputDepartamento",
        "javax.faces.partial.execute": "@all",
        "javax.faces.partial.render": "accordion",
        "javax.faces.behavior.event": "change",
        "javax.faces.partial.event": "change",
        "javax.faces.ViewState": viewstate,
        **_campos_filtro(codigo_departamento, FILAS_POR_PAGINA),
    }
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
        "javax.faces.ViewState": viewstate,
        **_campos_filtro(codigo_departamento, rows),
    }
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


def obtener_conteo_marcadores_por_departamento():
    """Un solo GET: {departamento: cantidad de plazas según el mapa}."""
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    titulos = re.findall(r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'", r.text)
    contador = Counter()
    for t in titulos:
        contador[t.split(" - ")[0].strip()] += 1
    return dict(contador)


# ============================================================
# FECHAS
# ============================================================

def parsear_fecha_cierre(cierre_texto):
    if not cierre_texto:
        return None
    try:
        return datetime.strptime(cierre_texto.strip(), "%d/%m/%Y a las %H:%M").replace(tzinfo=ZONA_COLOMBIA)
    except ValueError:
        return None


def limpiar_plazas_vencidas(plazas):
    ahora = _ahora()
    vigentes, vencidas = [], []
    for p in plazas:
        fc = parsear_fecha_cierre(p.get("cierre"))
        (vencidas if fc and fc <= ahora else vigentes).append(p)
    return vigentes, vencidas


def purgar_vencidas():
    with lock_json:
        plazas = cargar_datos_anteriores()
        vigentes, vencidas = limpiar_plazas_vencidas(plazas)
        if vencidas:
            guardar_datos_actuales(vigentes)
    return len(vencidas)


def contar_plazas_por_activacion(plazas):
    hoy = _ahora().date()
    ayer = hoy - timedelta(days=1)
    c_hoy = c_ayer = 0
    for p in plazas:
        fc = parsear_fecha_cierre(p.get("cierre"))
        if fc:
            activ = (fc - timedelta(days=1)).date()
            if activ == hoy:
                c_hoy += 1
            elif activ == ayer:
                c_ayer += 1
    return c_hoy, c_ayer


def es_plaza_nueva(p, desde=None):
    """🆕 = la plaza apareció DESPUÉS de la última vez que este chat recibió el resumen completo."""
    fs = p.get("first_seen")
    if desde is None or not fs:
        return False
    try:
        return datetime.fromisoformat(fs) > desde
    except ValueError:
        return False


def _desde_ultimo_resumen(chat_id):
    valor = _leer_json(ARCHIVO_RESUMENES, {}).get(str(chat_id))
    try:
        return datetime.fromisoformat(valor) if valor else None
    except ValueError:
        return None


def _marcar_resumen_enviado(chat_id):
    with lock_json:
        datos = _leer_json(ARCHIVO_RESUMENES, {})
        datos[str(chat_id)] = _ahora().isoformat()
        _escritura_atomica_json(ARCHIVO_RESUMENES, datos)


# ============================================================
# FUSIÓN Y REGISTRO (ÚNICA VÍA DE ESCRITURA DE PLAZAS)
# ============================================================

def fusionar_plazas(plazas_bd, scrapeadas, departamento, cantidad_esperada=None):
    """
    Scrape completo -> reconcilia (elimina las que ya no están en ese depto).
    Scrape incompleto -> solo agrega/actualiza (nunca borra).
    """
    completo = bool(scrapeadas) and (cantidad_esperada is None or len(scrapeadas) >= cantidad_esperada)
    if not completo:
        print(f"⚠️ Scrape incompleto de {departamento}: {len(scrapeadas)}/{cantidad_esperada}. Solo merge aditivo.")
    dep = _norm(departamento)
    ids_scrap = {p["id"] for p in scrapeadas}
    por_id = {p["id"]: p for p in plazas_bd}
    if completo:
        por_id = {i: p for i, p in por_id.items()
                  if _norm(p.get("departamento")) != dep or i in ids_scrap}
    nuevas = set()
    for p in scrapeadas:
        if p["id"] in por_id:
            por_id[p["id"]].update(p)
        else:
            por_id[p["id"]] = dict(p)
            nuevas.add(p["id"])
    return list(por_id.values()), nuevas


def registrar_plazas(scrapeadas, departamento, cantidad_esperada=None, silencioso=False):
    """Fusiona y marca las nuevas con first_seen y notificada=False (o True si silencioso)."""
    ahora = _ahora().isoformat()
    with lock_json:
        bd = cargar_datos_anteriores()
        fusionadas, nuevas = fusionar_plazas(bd, scrapeadas, departamento, cantidad_esperada)
        for p in fusionadas:
            if p["id"] in nuevas:
                p["first_seen"] = ahora
                p["notificada"] = bool(silencioso)
        guardar_datos_actuales(fusionadas)
    return nuevas


# ============================================================
# TELEGRAM
# ============================================================

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
    return partes or [mensaje[:limite]]


def enviar_telegram(mensaje, chat_id=None):
    """Devuelve True solo si TODAS las partes se enviaron."""
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    destino = chat_id if chat_id is not None else TELEGRAM_CHAT_ID
    todo_ok = True
    for i, parte in enumerate(_dividir_mensaje(mensaje, 4000), start=1):
        enviada = False
        for _ in range(3):
            try:
                r = requests.post(url, data={"chat_id": destino, "text": parte,
                                             "parse_mode": "HTML",
                                             "disable_web_page_preview": "true"}, timeout=10)
                if r.status_code == 200:
                    enviada = True
                    break
                print(f"⚠️ Error Telegram (parte {i}): {r.status_code} - {r.text[:200]}")
                if r.status_code == 429:
                    try:
                        time.sleep(int(r.json().get("parameters", {}).get("retry_after", 2)))
                    except Exception:
                        time.sleep(2)
                else:
                    time.sleep(1)
            except Exception as e:
                print(f"⚠️ Error Telegram (parte {i}): {e}")
                time.sleep(1)
        todo_ok = todo_ok and enviada
    return todo_ok


def construir_alerta_nuevas(plazas):
    lineas = [f"🆕 <b>{len(plazas)} plaza(s) nueva(s) en Sistema Maestro</b>", ""]
    for p in sorted(plazas, key=lambda x: (x["departamento"], x["area"])):
        lineas.append(
            f"📌 <b>{html.escape(p['departamento'])}</b> · {html.escape(abreviar_area(p['area']))} "
            f"({html.escape(p['municipio'])} - {html.escape(p['zona_tipo'])})"
        )
        lineas.append(f"   ⏰ Cierra: {html.escape(p['cierre'])} · {p['postulados']} postulados")
    lineas += ["", f'🔗 <a href="{URL_PAGINA}">Ir a Sistema Maestro</a>']
    return "\n".join(lineas)


def notificar_nuevas_pendientes():
    """Envía las plazas con notificada=False y las marca SOLO si Telegram confirmó."""
    with lock_notificar:
        with lock_json:
            pendientes = [p for p in cargar_datos_anteriores() if p.get("notificada") is False]
        if not pendientes:
            return 0
        if not enviar_telegram(construir_alerta_nuevas(pendientes)):
            print("⚠️ No se pudo enviar la alerta; quedan pendientes para el próximo ciclo.")
            return 0
        ids = {p["id"] for p in pendientes}
        with lock_json:
            plazas = cargar_datos_anteriores()
            for p in plazas:
                if p["id"] in ids:
                    p["notificada"] = True
            guardar_datos_actuales(plazas)
        return len(pendientes)


def construir_resumen(plazas, encabezado=None, chat_id=None):
    hoy, ayer = contar_plazas_por_activacion(plazas)
    desde = _desde_ultimo_resumen(chat_id) if chat_id is not None else None
    lineas = ["🚨 <b>¡Plazas Sistema Maestro!</b> 🚨", ""]
    if encabezado:
        lineas.append(f"🔎 <b>Filtro:</b> {html.escape(encabezado)}")
    lineas += [
        f"🌎 <b>Total plazas activas:</b> {len(plazas)}",
        f"🆕 <b>Plazas de hoy:</b> {hoy}",
        f"📅 <b>Plazas de ayer:</b> {ayer}",
        "", "--- <b>TODAS LAS PLAZAS</b> ---", "",
    ]
    deptos = defaultdict(list)
    for p in plazas:
        deptos[p["departamento"]].append(p)
    if not deptos:
        lineas.append("No se encontraron plazas.")
    for depto in sorted(deptos):
        lineas.append(f"📌 <b>{html.escape(depto)}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            marca = " 🆕" if es_plaza_nueva(p, desde) else ""
            lineas.append(
                f"  • {html.escape(abreviar_area(p['area']))} "
                f"({html.escape(p['municipio'])} - {html.escape(p['zona_tipo'])}){marca} "
                f"– {p['postulados']} postulados"
            )
        lineas.append("")
    lineas += ["", f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>']
    return "\n".join(lineas)


# ============================================================
# CICLO PRINCIPAL
# ============================================================

def ciclo_rapido(forzar_todos=False):
    """
    1 GET al mapa; scrapea solo los departamentos cuyo conteo cambió
    (o todos si forzar_todos / si la base está vacía). Notifica nuevas al instante.
    """
    purgar_vencidas()
    conteo_mapa = obtener_conteo_marcadores_por_departamento()
    if not conteo_mapa:
        raise RuntimeError("El mapa no devolvió marcadores (¿cambió el HTML del sitio?)")

    # Base vacía (arranque en frío / JSON perdido): sembrar sin spamear.
    sembrando = not cargar_datos_anteriores()
    if sembrando:
        forzar_todos = True
        print("🌱 Base vacía: se siembra en silencio (sin notificar).")

    previo = _leer_json(ARCHIVO_CONTEOS, {})
    objetivo = [d for d, c in conteo_mapa.items() if forzar_todos or previo.get(d) != c]
    nuevo = dict(previo)
    total_enviadas = 0

    for depto in objetivo:
        try:
            esperado = conteo_mapa[depto]
            plazas = obtener_vacantes_por_departamento(depto)
            registrar_plazas(plazas, depto, esperado, silencioso=sembrando)
            if len(plazas) >= esperado:
                nuevo[depto] = esperado   # si quedó incompleto, se reintenta en el próximo ciclo
            if not sembrando:
                total_enviadas += notificar_nuevas_pendientes()  # aviso inmediato por depto
        except Exception as e:
            print(f"⚠️ Error scraping {depto}: {e}")

    _escritura_atomica_json(ARCHIVO_CONTEOS, nuevo)
    if not sembrando:
        total_enviadas += notificar_nuevas_pendientes()  # reintenta pendientes de ciclos previos
    return f"{len(objetivo)} depto(s) revisados, {total_enviadas} plaza(s) nueva(s) notificada(s)"


def hilo_rapido():
    print(f"🧵 Ciclo rápido iniciado (cada {INTERVALO_RAPIDO}s).")
    time.sleep(5)
    while True:
        if lock_rapido.acquire(blocking=False):
            try:
                _marcar_estado("rapido", ciclo_rapido())
            except Exception as e:
                _marcar_estado("rapido", f"Error: {str(e)[:150]}")
                print(f"⚠️ Error en ciclo rápido: {e}")
            finally:
                lock_rapido.release()
        time.sleep(INTERVALO_RAPIDO)


def hilo_barrido():
    print(f"🧵 Barrido completo iniciado (cada {INTERVALO_BARRIDO}s).")
    time.sleep(60)
    while True:
        if lock_barrido.acquire(blocking=False):
            try:
                _marcar_estado("barrido", ciclo_rapido(forzar_todos=True))
            except Exception as e:
                _marcar_estado("barrido", f"Error: {str(e)[:150]}")
                print(f"⚠️ Error en barrido completo: {e}")
            finally:
                lock_barrido.release()
        time.sleep(INTERVALO_BARRIDO)


# ============================================================
# MENÚ INTERACTIVO Y COMANDOS DE TELEGRAM
# ============================================================

lock_menu = threading.Lock()
estados_menu_chat = {}
MENU_TTL_SEGUNDOS = 3600


def _limpiar_menus_viejos():
    ahora = time.time()
    with lock_menu:
        for cid in [c for c, e in estados_menu_chat.items()
                    if ahora - e.get("ultima_actividad", 0) > MENU_TTL_SEGUNDOS]:
            estados_menu_chat.pop(cid, None)


def _valores_en_json(campo, excluir):
    vals = {(p.get(campo) or "").strip() for p in cargar_datos_anteriores()}
    return sorted(v for v in vals if v and v.lower() != excluir)


def _es_comando(texto, nombres):
    if not texto:
        return False
    cand = texto.strip().replace(f"@{TELEGRAM_BOT_USERNAME}", "").strip().lower()
    return cand in nombres


def _enviar_menu_principal(chat_id):
    _limpiar_menus_viejos()
    with lock_menu:
        estados_menu_chat[chat_id] = {"tipo": "menu_principal", "ultima_actividad": time.time()}
    enviar_telegram("📋 <b>Menú principal</b>\n\n1. Departamento\n2. Áreas\n\nResponde con el número de la opción.",
                    chat_id=chat_id)


def _enviar_lista(chat_id, tipo, titulo, opciones):
    if not opciones:
        enviar_telegram("No hay plazas guardadas todavía.", chat_id=chat_id)
        with lock_menu:
            estados_menu_chat.pop(chat_id, None)
        return
    with lock_menu:
        estados_menu_chat[chat_id] = {"tipo": tipo, "opciones": opciones, "ultima_actividad": time.time()}
    lineas = [f"<b>{titulo}</b>", ""] + [f"{i}. {n}" for i, n in enumerate(opciones, 1)] + ["", "Responde con el número."]
    enviar_telegram("\n".join(lineas), chat_id=chat_id)


def _procesar_seleccion_menu(chat_id, texto):
    with lock_menu:
        est = estados_menu_chat.get(chat_id)
    texto = (texto or "").strip()
    if not est or not re.fullmatch(r"\d+", texto):
        return False
    with lock_menu:
        if chat_id in estados_menu_chat:
            estados_menu_chat[chat_id]["ultima_actividad"] = time.time()
    sel = int(texto)
    tipo = est["tipo"]
    if tipo == "menu_principal":
        if sel == 1:
            _enviar_lista(chat_id, "departamento_lista", "📍 Elige un departamento:",
                          _valores_en_json("departamento", "sin departamento"))
        elif sel == 2:
            _enviar_lista(chat_id, "area_lista", "📚 Elige un área:",
                          _valores_en_json("area", "sin área"))
        else:
            enviar_telegram("Opción inválida. Responde 1 o 2.", chat_id=chat_id)
        return True
    if tipo in ("departamento_lista", "area_lista"):
        ops = est.get("opciones", [])
        if not 1 <= sel <= len(ops):
            enviar_telegram(f"Opción inválida. Responde un número entre 1 y {len(ops)}.", chat_id=chat_id)
            return True
        elegido = ops[sel - 1]
        campo, etiqueta = ("departamento", "Departamento") if tipo == "departamento_lista" else ("area", "Área")
        plazas = [p for p in cargar_datos_anteriores() if (p.get(campo) or "").strip() == elegido]
        enviar_telegram(construir_resumen(plazas, f"{etiqueta}: {elegido}", chat_id=chat_id), chat_id=chat_id)
        with lock_menu:
            estados_menu_chat.pop(chat_id, None)
        return True
    return False


def _procesar_comando_actualizar(chat_id):
    if not lock_barrido.acquire(blocking=False):
        enviar_telegram("⏳ Ya hay una actualización en curso. Intenta en un momento.", chat_id=chat_id)
        return
    try:
        enviar_telegram("🔎 Actualizando plazas, dame un momento...", chat_id=chat_id)
        resultado = ciclo_rapido(forzar_todos=True)
        _marcar_estado("barrido", resultado)
        if enviar_telegram(construir_resumen(cargar_datos_anteriores(), chat_id=chat_id), chat_id=chat_id):
            _marcar_resumen_enviado(chat_id)
    except Exception as e:
        enviar_telegram(f"⚠️ Error al actualizar: {str(e)[:200]}", chat_id=chat_id)
    finally:
        lock_barrido.release()


@app.route("/telegram-webhook", methods=["POST"])
def telegram_webhook():
    if TELEGRAM_WEBHOOK_SECRET:
        if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != TELEGRAM_WEBHOOK_SECRET:
            return {"ok": False}, 403
    update = request.get_json(silent=True) or {}
    mensaje = update.get("message") or update.get("edited_message") or {}
    texto = mensaje.get("text", "")
    chat_id = (mensaje.get("chat") or {}).get("id")
    if chat_id is None:
        return {"ok": True}, 200
    if _es_comando(texto, ("menu", "menú", "/menu", "/menú")):
        _enviar_menu_principal(chat_id)
    elif _procesar_seleccion_menu(chat_id, texto):
        pass
    elif _es_comando(texto, ("actualizar", "/actualizar")):
        threading.Thread(target=_procesar_comando_actualizar, args=(chat_id,), daemon=True).start()
    return {"ok": True}, 200


@app.route("/set-webhook")
def set_webhook():
    url_publica = request.host_url.rstrip("/") + "/telegram-webhook"
    payload = {"url": url_publica}
    if TELEGRAM_WEBHOOK_SECRET:
        payload["secret_token"] = TELEGRAM_WEBHOOK_SECRET
    try:
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/setWebhook", data=payload, timeout=10)
        return {"webhook_configurado": url_publica, "respuesta_telegram": r.json()}
    except Exception as e:
        return {"error": str(e)}, 500


# ============================================================
# ENDPOINTS HTTP
# ============================================================

@app.route("/check")
def check():
    """Ciclo rápido en segundo plano (apto para cron-job.org)."""
    if not lock_rapido.acquire(blocking=False):
        return {"resultado": "Ya hay un ciclo en curso."}, 409

    def tarea():
        try:
            _marcar_estado("rapido", ciclo_rapido())
        except Exception as e:
            _marcar_estado("rapido", f"Error: {str(e)[:150]}")
        finally:
            lock_rapido.release()
    threading.Thread(target=tarea, daemon=True).start()
    return {"resultado": "Tarea iniciada en segundo plano"}, 202


@app.route("/check-force")
def check_force():
    """Barrido completo + resumen al chat por defecto, en segundo plano."""
    threading.Thread(target=_procesar_comando_actualizar, args=(TELEGRAM_CHAT_ID,), daemon=True).start()
    return {"resultado": "Barrido completo iniciado; el resumen llegará por Telegram."}, 202


@app.route("/status")
def status():
    plazas = cargar_datos_anteriores()
    with lock_estado:
        return {
            "intervalo_rapido_s": INTERVALO_RAPIDO,
            "intervalo_barrido_s": INTERVALO_BARRIDO,
            "total_plazas": len(plazas),
            "pendientes_de_notificar": sum(1 for p in plazas if p.get("notificada") is False),
            "rapido": estado["rapido"],
            "barrido": estado["barrido"],
        }


@app.route("/debug-nuevas")
def debug_nuevas():
    plazas = cargar_datos_anteriores()
    filas = [{
        "departamento": p.get("departamento"), "municipio": p.get("municipio"), "area": p.get("area"),
        "cierre": p.get("cierre"), "first_seen": p.get("first_seen"),
        "notificada": p.get("notificada"),
    } for p in plazas]
    filas.sort(key=lambda f: f["first_seen"] or "", reverse=True)
    return {"ahora": _ahora().isoformat(), "total": len(filas), "detalle": filas}


@app.route("/verjson")
def verjson():
    return {"ruta": os.path.abspath(ARCHIVO_DATOS), "contenido": cargar_datos_anteriores()}


@app.route("/departamentos")
def departamentos():
    try:
        mapa = obtener_conteo_marcadores_por_departamento()
    except Exception as e:
        return {"error": f"Error de conexión: {e}"}, 500
    en_json = Counter((p.get("departamento") or "").strip() for p in cargar_datos_anteriores())
    lista = [{"nombre": n, "cantidad": c, "en_json": en_json.get(n, 0)} for n, c in mapa.items()]
    lista.sort(key=lambda x: x["cantidad"], reverse=True)
    return {"departamentos": lista, "total": sum(mapa.values()), "departamentos_unicos": len(lista)}


@app.route("/agregar-departamento", methods=["POST"])
def agregar_departamento():
    """Siembra manual de un departamento (sin notificar)."""
    try:
        data = request.get_json(silent=True) or {}
        nombre = (data.get("departamento") or "").strip()
        if not nombre:
            return {"error": "Se requiere el nombre del departamento"}, 400
        try:
            plazas = obtener_vacantes_por_departamento(nombre)
        except ValueError as e:
            return {"error": str(e)}, 400
        if not plazas:
            return {"error": f"No se encontraron plazas para '{nombre}'."}, 404
        try:
            esperado = obtener_conteo_marcadores_por_departamento().get(nombre)
        except Exception:
            esperado = None
        nuevas = registrar_plazas(plazas, nombre, esperado, silencioso=True)
        return {"mensaje": f"Se procesaron {len(plazas)} plazas de '{nombre}'",
                "plazas_encontradas": len(plazas), "plazas_nuevas": len(nuevas),
                "total_plazas_en_json": len(cargar_datos_anteriores())}
    except Exception as e:
        return {"error": f"Error al agregar departamento: {e}"}, 500


@app.route("/limpiar-vencidas", methods=["POST"])
def limpiar_vencidas():
    try:
        n = purgar_vencidas()
        return {"mensaje": f"Se eliminaron {n} plazas vencidas.", "eliminadas": n,
                "restantes": len(cargar_datos_anteriores())}
    except Exception as e:
        return {"error": str(e)}, 500


@app.route("/limpiar-json", methods=["POST"])
def limpiar_json():
    """Reinicia la base. El próximo ciclo siembra en silencio (sin spam)."""
    try:
        with lock_json:
            for ruta in (ARCHIVO_DATOS, ARCHIVO_CONTEOS):
                if os.path.exists(ruta):
                    os.remove(ruta)
        return {"mensaje": "Base reiniciada. El próximo ciclo la volverá a sembrar sin notificar."}
    except Exception as e:
        return {"error": f"Error al limpiar JSON: {e}"}, 500


@app.route("/cargar-json", methods=["POST"])
def cargar_json():
    try:
        data = json.loads(request.get_data(as_text=True) or "")
    except json.JSONDecodeError as e:
        return {"error": f"JSON inválido: {e}"}, 400
    if not isinstance(data, list) or not data:
        return {"error": "El JSON debe ser una lista no vacía"}, 400
    for p in data:
        p.setdefault("notificada", True)
    guardar_datos_actuales(data)
    return {"mensaje": f"JSON guardado ({len(data)} plazas)"}


PAGINA_HOME = """<!DOCTYPE html><html><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Vigilante de Vacantes</title><style>
body{font-family:Arial,sans-serif;margin:24px}button{padding:10px 16px;margin:4px;cursor:pointer}
pre{background:#f4f4f4;padding:12px;border-radius:6px;overflow:auto;max-height:420px}
.card{border:1px solid #ddd;padding:16px;margin-bottom:16px;border-radius:8px}</style></head><body>
<h1>🕵️ Vigilante de Vacantes</h1>
<div class="card"><h2>Acciones</h2>
<button onclick="get('/check')">🚀 Ciclo rápido</button>
<button onclick="get('/check-force')">📢 Barrido completo + resumen</button>
<button onclick="post('/limpiar-vencidas')">🗑️ Eliminar vencidas</button>
<button onclick="if(confirm('¿Reiniciar la base?'))post('/limpiar-json')">♻️ Reiniciar base</button>
<div id="res" style="margin-top:10px;color:green"></div></div>
<div class="card"><h2>Estado</h2><pre id="st">...</pre></div>
<div class="card"><h2>Plazas (JSON)</h2><pre id="js">__JSON__</pre></div>
<script>
const out=t=>document.getElementById('res').textContent=t;
function get(u){out('⏳...');fetch(u).then(r=>r.json()).then(d=>{out('✅ '+(d.resultado||JSON.stringify(d)));refrescar()}).catch(e=>out('❌ '+e))}
function post(u){out('⏳...');fetch(u,{method:'POST'}).then(r=>r.json()).then(d=>{out('✅ '+(d.mensaje||d.error));refrescar()}).catch(e=>out('❌ '+e))}
function refrescar(){
 fetch('/status').then(r=>r.json()).then(d=>document.getElementById('st').textContent=JSON.stringify(d,null,2));
 fetch('/verjson',{cache:'no-store'}).then(r=>r.json()).then(d=>document.getElementById('js').textContent=JSON.stringify(d.contenido,null,2));
}
refrescar();setInterval(refrescar,30000);
</script></body></html>"""


@app.route("/")
def home():
    return PAGINA_HOME.replace(
        "__JSON__", html.escape(json.dumps(cargar_datos_anteriores(), indent=2, ensure_ascii=False)))


# ============================================================
# ARRANQUE
# ============================================================
# Usa: gunicorn app:app --workers 1 --threads 4 --timeout 120
# Con más de 1 worker los hilos arrancarían una vez por worker y duplicarían trabajo.
threading.Thread(target=hilo_rapido, daemon=True).start()
threading.Thread(target=hilo_barrido, daemon=True).start()


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
