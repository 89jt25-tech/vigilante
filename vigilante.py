import requests
import hashlib
import os
import re
import json
from collections import Counter

# ========================
# CONFIGURACIÓN
# ========================
TELEGRAM_TOKEN = "8728019584:AAG3kwzK3qqhEMWvvev2LqcvSlBAPGS57-M"
TELEGRAM_CHAT_ID = "6944650611"

# --- CONFIGURACIÓN DE GITHUB GIST (MEMORIA EN LA NUBE) ---
# 1. Ve a https://github.com/settings/tokens y crea un token con permiso "gist".
# 2. Pon el token aquí:
GITHUB_TOKEN = "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"  # <--- CREA ESTE TOKEN AHORA (es GRATIS)
GIST_ID = "TU_GIST_ID_AQUI"  # <--- LO CREAREMOS MÁS ABAJO, déjalo así por ahora.

URL_PAGINA = "https://sistemamaestro.mineducacion.gov.co/SistemaMaestro/busquedaVacantes.xhtml"
ARCHIVO_NOMBRE = "hash_mapa.txt"

# ========================
# FUNCIONES PARA GIST (MEMORIA PERMANENTE)
# ========================
def leer_hash_de_gist():
    """Lee el hash guardado en el Gist"""
    url = f"https://api.github.com/gists/{GIST_ID}"
    headers = {"Authorization": f"token {GITHUB_TOKEN}"}
    try:
        response = requests.get(url, headers=headers)
        if response.status_code == 200:
            data = response.json()
            # El contenido está en data['files'][ARCHIVO_NOMBRE]['content']
            if ARCHIVO_NOMBRE in data['files']:
                return data['files'][ARCHIVO_NOMBRE]['content'].strip()
        return ""
    except:
        return ""

def guardar_hash_en_gist(hash_nuevo):
    """Actualiza el Gist con el nuevo hash"""
    url = f"https://api.github.com/gists/{GIST_ID}"
    headers = {"Authorization": f"token {GITHUB_TOKEN}"}
    data = {
        "files": {
            ARCHIVO_NOMBRE: {
                "content": hash_nuevo
            }
        }
    }
    try:
        requests.patch(url, headers=headers, json=data)
        print("✅ Hash guardado en la nube (Gist).")
    except Exception as e:
        print(f"❌ Error al guardar en Gist: {e}")

def crear_gist_si_no_existe():
    """Crea un Gist nuevo si es la primera vez y devuelve su ID"""
    global GIST_ID
    if GIST_ID == "TU_GIST_ID_AQUI":
        url = "https://api.github.com/gists"
        headers = {"Authorization": f"token {GITHUB_TOKEN}"}
        data = {
            "description": "Hash para vigilante de vacantes MEN",
            "public": False,
            "files": {
                ARCHIVO_NOMBRE: {
                    "content": ""
                }
            }
        }
        response = requests.post(url, headers=headers, json=data)
        if response.status_code == 201:
            gist_data = response.json()
            GIST_ID = gist_data['id']
            print(f"✅ Gist creado con ID: {GIST_ID}")
            print(f"⚠️ COPIA ESTE ID y reemplázalo en la variable GIST_ID dentro del código.")
            return GIST_ID
        else:
            print("❌ Error al crear el Gist. Revisa tu token.")
            exit()
    return GIST_ID

# ========================
# ENVIAR A TELEGRAM
# ========================
def enviar_telegram(mensaje):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    datos = {"chat_id": TELEGRAM_CHAT_ID, "text": mensaje, "parse_mode": "HTML"}
    try:
        requests.post(url, data=datos, timeout=10)
        print("📨 Notificación enviada")
    except Exception as e:
        print(f"❌ Error: {e}")

# ========================
# EXTRAER DATOS DE LA PÁGINA
# ========================
def extraer_marcadores(html):
    patron = r'title:\s*[\'"]([^\'"]+)[\'"]'
    coincidencias = re.findall(patron, html, re.DOTALL)
    if not coincidencias:
        return None
    contador = Counter(coincidencias)
    return dict(sorted(contador.items()))

# ========================
# EJECUTAR VIGILANTE
# ========================
def ejecutar_vigilante():
    print("🔄 Revisando página del MEN...")
    headers = {"User-Agent": "Mozilla/5.0"}
    
    try:
        response = requests.get(URL_PAGINA, headers=headers, timeout=30)
        html = response.text
        
        marcadores = extraer_marcadores(html)
        if marcadores is None:
            return "No se encontraron marcadores"
        
        # Construir resumen
        resumen = "\n".join([f"{dep}: {cant}" for dep, cant in marcadores.items()])
        hash_actual = hashlib.md5(resumen.encode('utf-8')).hexdigest()
        
        # --- MEMORIA EN LA NUBE (Gist) ---
        # Asegurarse de que existe el Gist
        crear_gist_si_no_existe()
        
        # Leer hash anterior desde la nube
        hash_anterior = leer_hash_de_gist()
        
        if hash_actual != hash_anterior:
            mensaje = "🚨 <b>¡CAMBIO EN VACANTES!</b> 🚨\n\n"
            mensaje += "📋 <b>Estado actual por región:</b>\n<pre>" + resumen + "</pre>"
            enviar_telegram(mensaje)
            guardar_hash_en_gist(hash_actual)
            return "Notificación enviada"
        else:
            return "Sin cambios"
            
    except Exception as e:
        print(f"❌ Error: {e}")
        enviar_telegram(f"⚠️ Error: {str(e)[:200]}")
        return f"Error"

# ========================
# EJECUCIÓN
# ========================
if __name__ == "__main__":
    resultado = ejecutar_vigilante()
    print(f"Resultado: {resultado}")
