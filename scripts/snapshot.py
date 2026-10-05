#!/usr/bin/env python3
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[1]
excluded={'.git','.lake','.cache','.toolchain','.build','build','__pycache__','evidence','reports'}
files=[]
for p in ROOT.rglob('*'):
    if not p.is_file() or excluded.intersection(p.relative_to(ROOT).parts):continue
    rel=p.relative_to(ROOT).as_posix()
    if rel.startswith('.github/') or p.suffix=='.md' or p.suffix=='.zip':continue
    files.append(p)
for p in sorted(files):print(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix())
