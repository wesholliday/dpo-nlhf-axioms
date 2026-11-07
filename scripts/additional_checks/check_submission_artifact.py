#!/usr/bin/env python3
"""Camera-ready package-only verification; no training or numerical solver."""
from pathlib import Path
import runpy
if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[1] / 'verify_camera_ready.py'), run_name='__main__')
