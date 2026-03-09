"""
utils_env.py — Carga variables de entorno desde archivo .envvars (local)
o directamente del sistema (Render, Railway, etc.)
"""

import os

def load_env(path=".envvars"):
    """
    Intenta cargar variables desde el archivo path.
    Si el archivo no existe (ej: en Render), usa las variables
    del entorno del sistema directamente, sin error.
    """
    if os.path.exists(path):
        try:
            from dotenv import load_dotenv
            load_dotenv(dotenv_path=path, override=False)
            print(f"[utils_env] Variables cargadas desde '{path}'")
        except ImportError:
            _parse_envfile(path)
    else:
        print(f"[utils_env] Archivo '{path}' no encontrado — usando variables del sistema (modo cloud)")


def _parse_envfile(path):
    """Fallback: parsea el archivo .envvars manualmente sin dependencias."""
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if "=" in line:
                key, _, value = line.partition("=")
                key = key.strip()
                value = value.strip().strip('"').strip("'")
                if key and key not in os.environ:
                    os.environ[key] = value
