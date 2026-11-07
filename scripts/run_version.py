#!/usr/bin/env python3
"""Run an archived source version with the supplement root as working directory.

This launcher chooses imports and forwards arguments; it does not change a
training module, seed, loss, optimizer, reference, or scientific parameter.
"""
import os
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parents[1]
VERSIONS = ('historical', 'completion_2026_11_01', 'initial_theory_audit')
if len(sys.argv) < 3 or sys.argv[1] not in VERSIONS:
    raise SystemExit('Usage: python scripts/run_version.py {' + ','.join(VERSIONS) + '} scripts.MODULE [arguments]')
version, module = sys.argv[1:3]
if not module.startswith('scripts.'):
    raise SystemExit('Expected a scripts.* module')
os.chdir(ROOT)
sys.path.insert(0, str(ROOT / 'code_versions' / version))
sys.argv = [module, *sys.argv[3:]]
runpy.run_module(module, run_name='__main__', alter_sys=True)
