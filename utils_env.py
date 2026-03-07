"""
utils_env.py — Carga variables de entorno desde un archivo .envvars
Uso: from utils_env import load_env; load_env(".envvars")
"""

import os


def load_env(path=".envvars"):
    """
    Lee un archivo de variables de entorno linea por linea.
    Formato: CLAVE=VALOR
    Ignora lineas vacias y comentarios (#).
    No sobreescribe variables ya definidas en el entorno del sistema.
    """
    if not os.path.exists(path):
        print(f"[utils_env] Archivo {path} no encontrado, usando variables del sistema.")
        return

    with open(path, "r", encoding="utf-8") as f:
        for linea in f:
            linea = linea.strip()
            if not linea or linea.startswith("#"):
                continue
            if "=" not in linea:
                continue
            clave, _, valor = linea.partition("=")
            clave  = clave.strip()
            valor  = valor.strip()

            # Remover comillas opcionales alrededor del valor
            if len(valor) >= 2 and valor[0] in ('"', "'") and valor[-1] == valor[0]:
                valor = valor[1:-1]

            # No sobreescribir si ya esta definida (ej: en Render/Railway)
            if clave and clave not in os.environ:
                os.environ[clave] = valor
