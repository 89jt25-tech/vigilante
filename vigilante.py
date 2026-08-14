from flask import Flask, request
import requests
import os
import re
import json
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
    "bogotá": "919",
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
MAX_PAGINAS = 60
FILAS_POR_PAGINA = 6

# ============================================================
# FUNCIONES ELIMINADAS (comentadas o simplemente no existen)
# ============================================================

# Carga manual de un JSON externo
# --------------------------------------------------------

def cargar_datos_anteriores():
    if os.path.exists(ARCHIVO_DATOS):
        try:
            with open(ARCHIVO_DATOS, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return []
    return []

def guardar_datos_actuales(plazas):
    if plazas:
        with open(ARCHIVO_DATOS, "w", encoding="utf-8") as f:
            json.dump(plazas, f, ensure_ascii=False, indent=2)
    else:
        print("⚠️ Se intentó guardar una lista vacía de plazas. No se sobrescribió el archivo.")

# También necesitamos obtener_total_plazas_mapa y guardar_total_mapa_actual para mantener consistencia
def obtener_total_plazas_mapa():
    r = requests.get(URL_PAGINA, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    patron = r"alt:\s*'DEP-\d+',\s*title:\s*'([^']+)'"
    coincidencias = re.findall(patron, r.text)
    return len(coincidencias)

def guardar_total_mapa_actual(total_mapa):
    with open(ARCHIVO_TOTAL_MAPA, "w", encoding="utf-8") as f:
        json.dump({"total_mapa": total_mapa}, f, ensure_ascii=False, indent=2)

#De forma manual desde la interfaz web y automatica
# --------------------------------------------------------

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
        zona = extraer_campo(panel, r"Zona:")
        departamento = extraer_campo(panel, r"Departamento:")
        municipio = extraer_campo(panel, r"Municipio:")

        id_plaza = f"{departamento}|{area}|{zona}|{municipio}|{cierre}|{secretaria}|{cargo}|{tipo}"
        id_plaza = id_plaza.lower().replace(" ", "_")

        vacante = {
            "id": id_plaza,
            "area": area or "Sin área",
            "secretaria": secretaria or "Sin secretaría",
            "zona": zona or "Sin zona",
            "departamento": departamento or "Sin departamento",
            "municipio": municipio or "Sin municipio",
            "tipo_priorizacion": tipo or "Sin tipo",
            "cierre": cierre,
            "postulados": postulados,
            "cargo": cargo or "Sin cargo",
        }
        vacantes.append(vacante)
    return vacantes

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
    Ahora usa form-busqueda:idInputDepartamento en lugar de idInputSecretaria.
    """
    data = {
        "javax.faces.partial.ajax": "true",
        "javax.faces.source": "form-busqueda:idInputDepartamento",  # Cambio aquí
        "javax.faces.partial.execute": "@all",
        "javax.faces.partial.render": "accordion",
        "javax.faces.behavior.event": "change",
        "javax.faces.partial.event": "change",
        "form-busqueda": "form-busqueda",
        "javax.faces.ViewState": viewstate,
        "form-busqueda:idInputSecretaria_focus": "",
        "form-busqueda:idInputSecretaria_input": "",          # Vacío
        "form-busqueda:idInputDepartamento_focus": "",
        "form-busqueda:idInputDepartamento_input": codigo_departamento,  # Nuevo campo
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
    Pide una página de resultados YA con el filtro de departamento activo.
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
        "form-busqueda:idInputSecretaria_input": "",          # Vacío
        "form-busqueda:idInputDepartamento_focus": "",
        "form-busqueda:idInputDepartamento_input": codigo_departamento,  # Cambio
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
    return resultado["html"], nuevo_viewstate

def obtener_vacantes_por_departamento(nombre_departamento):
    """
    Obtiene TODAS las vacantes de un departamento usando el filtro.
    """
    nombre_clean = nombre_departamento.lower().strip()
    codigo = DEPARTAMENTOS_CODIGOS.get(nombre_clean)
    if not codigo:
        # Búsqueda flexible
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

    # Aplicar filtro de departamento
    _, viewstate = cambiar_filtro_departamento(session, viewstate, codigo)

    # Paginar resultados
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
    - Plazas existentes: se actualizan (postulados, etc.)
    - Plazas nuevas: se agregan
    - Plazas que no aparecen hoy: se dejan intactas
    """
    bd_por_id = {p["id"]: dict(p) for p in plazas_bd}
    ids_nuevas = set()
    for p in plazas_scrapeadas:
        if p["id"] in bd_por_id:
            # Actualizar datos de la plaza existente
            bd_por_id[p["id"]].update(p)
        else:
            bd_por_id[p["id"]] = dict(p)
            ids_nuevas.add(p["id"])
    return list(bd_por_id.values()), ids_nuevas

#eliminar plaza
#--------------
def parsear_fecha_cierre(cierre_texto):
    """
    Convierte '01/08/2026 a las 11:30' a datetime con zona horaria de Colombia.
    Devuelve None si el texto viene vacío o con formato inesperado.
    """
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

#--------------

def ejecutar_vigilante(notificar_siempre=False):
    """
    Flujo principal automatizado:
    1. Limpiar plazas vencidas del JSON.
    2. Obtener total del mapa y total del JSON.
    3. Si faltan plazas, agregar todas las pendientes por departamento.
    4. Detectar cambios (plazas nuevas, postulados que cambiaron).
    5. Notificar por Telegram (si hay cambios o si se fuerza).
    """
    try:
        # 1. Cargar JSON actual (base de datos)
        plazas_bd = cargar_datos_anteriores()
        total_json_actual = len(plazas_bd)

        # Guardar copia ANTES de cualquier modificación (para detectar cambios)
        plazas_antes = plazas_bd.copy()

        # 2. Limpiar plazas vencidas
        plazas_vigentes, plazas_vencidas = limpiar_plazas_vencidas(plazas_bd)
        if plazas_vencidas:
            guardar_datos_actuales(plazas_vigentes)
            plazas_bd = plazas_vigentes
            total_json_actual = len(plazas_bd)

        # 3. Obtener total del mapa actual y el anterior (de total_mapa.json)
        total_mapa = obtener_total_plazas_mapa()
        total_mapa_anterior = cargar_total_mapa_anterior()

        # 4. Si hay plazas faltantes, agregarlas automáticamente
        if total_mapa > total_json_actual:
            departamentos_pendientes = obtener_departamentos_pendientes()
            for depto in departamentos_pendientes:
                try:
                    plazas_depto = obtener_vacantes_por_departamento(depto)
                    plazas_bd, _ = fusionar_plazas(plazas_bd, plazas_depto)
                    guardar_datos_actuales(plazas_bd)
                except Exception as e:
                    print(f"Error agregando {depto}: {e}")
            # Después de agregar, recargar plazas_bd y total_json_actual
            plazas_bd = cargar_datos_anteriores()
            total_json_actual = len(plazas_bd)

        # 5. Detectar cambios comparando plazas_bd con plazas_antes
        cambios = detectar_cambios(plazas_bd, plazas_antes)

        # 6. Determinar si notificar
        hay_cambios = (
            (total_mapa != total_mapa_anterior) or
            cambios["total_nuevas"] > 0 or
            cambios["total_actualizadas"] > 0 or
            len(plazas_vencidas) > 0
        )
        debe_notificar = hay_cambios or notificar_siempre

        if debe_notificar:
            # Extraer IDs de plazas nuevas para el resumen
            ids_nuevas = {p["id"] for p in cambios["nuevas"]}
            resumen = construir_resumen(
                plazas_bd,
                plazas_bd,  # plazas_scrapeadas (usamos las mismas, pues ya están actualizadas)
                total_mapa,
                ids_nuevas,
                total_mapa_anterior
            )
            enviar_telegram(resumen)
            # Guardar total del mapa actual para futuras comparaciones
            guardar_total_mapa_actual(total_mapa)
            return "Notificación enviada."
        else:
            # Actualizar total_mapa.json aunque no haya cambios (para mantener sincronía)
            guardar_total_mapa_actual(total_mapa)
            return "Sin cambios notificables."

    except Exception as e:
        enviar_telegram(f"⚠️ Error en vigilante: {str(e)[:200]}")
        return f"Error: {str(e)[:100]}"

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

def guardar_total_mapa_actual(total_mapa):
    with open(ARCHIVO_TOTAL_MAPA, "w", encoding="utf-8") as f:
        json.dump({"total_mapa": total_mapa}, f, ensure_ascii=False, indent=2)

def obtener_departamentos_pendientes():
    """
    Devuelve una lista con los nombres de los departamentos que tienen
    plazas en el mapa pero no están completas en el JSON.
    """
    # Obtener departamentos del mapa
    deptos_mapa = obtener_departamentos_del_mapa()
    # Cargar JSON y contar plazas por departamento
    plazas_json = cargar_datos_anteriores()
    contador_json = defaultdict(int)
    for p in plazas_json:
        depto = p.get("departamento", "").strip()
        if depto:
            contador_json[depto] += 1

    # Obtener conteo por departamento desde el mapa
    # (reutilizamos la lógica de /departamentos)
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
    - plazas_bd: Todas las plazas en JSON (histórico completo)
    - plazas_scrapeadas: Plazas de hoy (tabla) - en este flujo es igual a plazas_bd
    - total_mapa: Total en el mapa
    - ids_nuevas: IDs de plazas nuevas detectadas hoy
    - total_mapa_anterior: Total del mapa en la ejecución anterior
    """
    ids_nuevas = ids_nuevas or set()

    total_hoy_json, total_ayer_calculado = contar_plazas_por_activacion(plazas_bd)

    # Agrupar TODAS las plazas del JSON por departamento
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
        lineas.append(f"📌 <b>{depto}</b>")
        for p in sorted(deptos[depto], key=lambda x: x["area"]):
            es_nueva = p["id"] in ids_nuevas
            
            cambio = None
            if not es_nueva and p["id"] in anteriores_por_id:
                anterior = anteriores_por_id[p["id"]]
                if p["postulados"] != anterior["postulados"]:
                    cambio = (anterior["postulados"], p["postulados"])
            
            if es_nueva:
                linea = f"  • {p['area']} ({p['municipio']}) 🆕 – {p['postulados']} postulados"
            else:
                flecha = ""
                if cambio:
                    if cambio[1] > cambio[0]:
                        flecha = " ↑"
                    elif cambio[1] < cambio[0]:
                        flecha = " ↓"
                linea = f"  • {p['area']} ({p['municipio']}){flecha} – {p['postulados']} postulados"
            
            lineas.append(linea)
        lineas.append("")

    lineas.append("")
    lineas.append(f'🔗 <a href="{URL_PAGINA}">Ir a la página Sistema Maestro</a>')

    return "\n".join(lineas)

def enviar_telegram(mensaje):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    datos = {"chat_id": TELEGRAM_CHAT_ID, "text": mensaje, "parse_mode": "HTML"}
    try:
        requests.post(url, data=datos, timeout=10)
    except Exception as e:
        print(f"Error Telegram: {e}")

# ========== ENDPOINTS DE DIAGNÓSTICO AGREGADOS ==========

@app.route("/check")
def check():
    resultado = ejecutar_vigilante(notificar_siempre=False)
    return {"resultado": resultado}

@app.route("/check-force")
def check_force():
    resultado = ejecutar_vigilante(notificar_siempre=True)
    return {"resultado": resultado}

@app.route("/")
def home():
    ruta = os.path.abspath(ARCHIVO_DATOS)
    contenido = "No existe"
    if os.path.exists(ruta):
        with open(ruta, "r", encoding="utf-8") as f:
            contenido = json.load(f)

    html = """
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
                fetch('/verjson')
                    .then(response => response.json())
                    .then(data => {
                        const pre = document.querySelector('pre');
                        if (pre) {
                            pre.textContent = JSON.stringify(data.contenido, null, 2);
                        }
                    })
                    .catch(error => console.error('Error al actualizar JSON:', error));
            }

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
                        // Refrescar la tabla de departamentos
                        verDepartamentos();
                        // Refrescar el contenido del JSON en el <pre>
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

                // Paso 1: Obtener la lista de departamentos
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

                        // Filtrar departamentos que necesitan ser agregados (en_json < cantidad)
                        const pendientes = data.departamentos.filter(d => d.en_json < d.cantidad);
                        
                        if (pendientes.length === 0) {
                            resultadoDiv.innerHTML = '✅ Todos los departamentos ya están completos. ¡No hay nada que agregar!';
                            alert('✅ Todos los departamentos ya están completos.');
                            btn.disabled = false;
                            btn.textContent = '🚀 Agregar todos los departamentos pendientes';
                            return;
                        }

                        // Mostrar cuántos departamentos vamos a procesar
                        resultadoDiv.innerHTML = `⏳ Agregando plazas de ${pendientes.length} departamento(s) pendientes... (0/${pendientes.length})`;
                        
                        // Paso 2: Procesar cada departamento pendiente en secuencia
                        let procesados = 0;
                        let totalAgregados = 0;
                        let errores = [];

                        function procesarSiguiente() {
                            if (procesados >= pendientes.length) {
                                // Todos procesados
                                const mensaje = `✅ Proceso completado. Se agregaron plazas de ${totalAgregados} departamento(s). ${errores.length > 0 ? 'Hubo ' + errores.length + ' error(es).' : ''}`;
                                resultadoDiv.innerHTML = mensaje;
                                alert(mensaje);
                                // Refrescar la tabla y el JSON para ver los cambios
                                verDepartamentos();
                                actualizarContenidoJSON();
                                btn.disabled = false;
                                btn.textContent = '🚀 Agregar todos los departamentos pendientes';
                                return;
                            }

                            const depto = pendientes[procesados];
                            const nombre = depto.nombre;
                            resultadoDiv.innerHTML = `⏳ Agregando plazas de ${nombre}... (${procesados + 1}/${pendientes.length})`;

                            // Llamar a agregarDepartamento (pero sin confirmación y sin alertas)
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

                        // Iniciar el procesamiento secuencial
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
                        // Refrescar la tabla de departamentos y el JSON mostrado
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
    html = html.replace(
        "__CONTENIDO_JSON__",
        json.dumps(contenido, indent=2, ensure_ascii=False)
    )
    return html

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

    # Guardar los datos
    guardar_datos_actuales(data)
    # También guardar el total del mapa actual
    try:
        total_mapa = obtener_total_plazas_mapa()
        guardar_total_mapa_actual(total_mapa)
    except Exception as e:
        # Si falla, no es crítico, pero lo registramos
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
        from collections import Counter
        headers = {"User-Agent": "Mozilla/5.0"}
        response = requests.get(URL_PAGINA, headers=headers, timeout=30)
        response.raise_for_status()

        # Extraer títulos de marcadores (departamentos con plazas)
        patron = r'L\.marker\(\[.*?\],\s*\{[^}]*title:\s*[\'"]([^\'"]+)[\'"][^}]*\}\)'
        coincidencias = re.findall(patron, response.text, re.DOTALL)
        if not coincidencias:
            patron2 = r'title:\s*[\'"]([^\'"]+)[\'"]'
            coincidencias = re.findall(patron2, response.text, re.DOTALL)

        if not coincidencias:
            return {"error": "No se encontraron departamentos"}, 404

        # Contar plazas por departamento en el mapa
        contador_mapa = Counter(coincidencias)

        # Cargar el JSON actual y contar plazas por departamento
        plazas_json = cargar_datos_anteriores()
        contador_json = defaultdict(int)
        for p in plazas_json:
            depto = p.get("departamento", "").strip()
            if depto:
                contador_json[depto] += 1

        # Construir la lista combinada
        departamentos = []
        for nombre, cantidad_mapa in contador_mapa.items():
            # Extraer solo el nombre del departamento (primera parte antes de " - ")
            nombre_depto = nombre.split(" - ")[0].strip()
            cantidad_json = contador_json.get(nombre_depto, 0)
            departamentos.append({
                "nombre": nombre_depto,
                "cantidad": cantidad_mapa,
                "en_json": cantidad_json
            })

        # Ordenar por cantidad (de mayor a menor)
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

        # Obtener plazas del departamento
        try:
            plazas_departamento = obtener_vacantes_por_departamento(departamento_nombre)
        except ValueError as e:
            return {"error": str(e)}, 400

        if not plazas_departamento:
            return {"error": f"No se encontraron plazas para '{departamento_nombre}'."}, 404

        # Cargar JSON anterior y fusionar
        plazas_bd = cargar_datos_anteriores()
        plazas_fusionadas, ids_nuevas = fusionar_plazas(plazas_bd, plazas_departamento)
        guardar_datos_actuales(plazas_fusionadas)

        # Actualizar también el total del mapa (para mantener consistencia)
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
            # Opcional: actualizar total_mapa.json con el nuevo conteo (si quieres)
            # total_mapa = obtener_total_plazas_mapa()
            # guardar_total_mapa_actual(total_mapa)
            return {
                "mensaje": f"Se eliminaron {len(vencidas)} plazas vencidas.",
                "eliminadas": len(vencidas),
                "restantes": len(vigentes)
            }, 200
        else:
            return {"mensaje": "No hay plazas vencidas.", "eliminadas": 0}, 200
    except Exception as e:
        return {"error": str(e)}, 500

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
