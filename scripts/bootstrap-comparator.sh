#!/usr/bin/env bash
# Fetch official pinned tools into an external cache; no checker source patches.
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
CACHE=${COMPARATOR_CACHE:-"${XDG_CACHE_HOME:-$HOME/.cache}/exact-hill-shares/comparator-lean4.19.0"}
export COMPARATOR_CACHE="$CACHE"
WITH_LANDRUN=0
if [[ ${1:-} == --with-landrun ]]; then WITH_LANDRUN=1; shift; fi
[[ $# == 0 ]] || { echo 'Usage: bootstrap-comparator.sh [--with-landrun]' >&2; exit 2; }
if [[ -n ${LEAN_HOME:-} ]]; then export PATH="$LEAN_HOME/bin:$PATH"; fi
lean --version | grep -q 'version 4.19.0,' || { echo 'Lean 4.19.0 is required.' >&2; exit 2; }
mkdir -p "$CACHE"
python3 - "$ROOT/comparator/PINS.json" "$CACHE" "$WITH_LANDRUN" <<'PY'
import hashlib, json, os, pathlib, subprocess, sys
pins = json.loads(pathlib.Path(sys.argv[1]).read_text())
cache = pathlib.Path(sys.argv[2]).resolve()
def run(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()
def checkout(key, dest):
    pin = pins[key]
    if not dest.exists():
        subprocess.run(['git', 'clone', '--no-checkout', pin['url'], str(dest)], check=True)
        subprocess.run(['git', 'checkout', '--detach', pin['rev']], cwd=dest, check=True)
    if run('git', 'rev-parse', 'HEAD', cwd=dest) != pin['rev']:
        raise SystemExit(f'{dest} has a different revision; use a fresh COMPARATOR_CACHE')
    return dest
up = checkout('comparator', cache/'source')
# Only metadata is adapted: the official pre-v25 Lean sources stay byte-identical.
allowed = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}
changed = set(run('git', 'diff', 'HEAD', '--name-only', cwd=up).splitlines())
if changed - allowed:
    raise SystemExit(f'Official comparator source modified: {sorted(changed - allowed)}')
if run('git', 'ls-files', '--others', '--exclude-standard', cwd=up):
    raise SystemExit('Unexpected untracked files in official comparator checkout')
(up/'lean-toolchain').write_text('leanprover/lean4:v4.19.0\n')
original = run('git', 'show', 'HEAD:lakefile.toml', cwd=up) + '\n'
(up/'lakefile.toml').write_text(original.replace('v4.24.0', 'v4.19.0'))
manifest = json.loads(run('git', 'show', 'HEAD:lake-manifest.json', cwd=up))
for dep in manifest['packages']:
    dep['rev'] = pins[dep['name']]['rev']
    dep['inputRev'] = 'v4.19.0'
(up/'lake-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
helper = pins['trusted_local_helper']
# The official development helper is deliberately outside the source deliverable.
content = subprocess.check_output(['git', 'show', helper['rev']+':'+helper['path']], cwd=up)
if hashlib.sha256(content).hexdigest() != helper['sha256']:
    raise SystemExit('Official trusted-local helper hash mismatch')
(cache/'trusted-local-landrun').write_bytes(content)
(cache/'trusted-local-landrun').chmod(0o755)
subprocess.run(['lake', 'build', 'lean4export', 'comparator'], cwd=up, check=True)
for dep in ('lean4export', 'lean4checker'):
    d = up/'.lake'/'packages'/dep
    if run('git', 'rev-parse', 'HEAD', cwd=d) != pins[dep]['rev']:
        raise SystemExit(f'{dep} revision mismatch')
    if run('git', 'status', '--porcelain', '--untracked-files=all', cwd=d):
        raise SystemExit(f'{dep} has modified or untracked sources')
(cache/'pins.json').write_text(json.dumps(pins, indent=2)+'\n')
if sys.argv[3] == '1':
    landrun = checkout('landrun', cache/'landrun-source')
    if run('git', 'status', '--porcelain', '--untracked-files=all', cwd=landrun):
        raise SystemExit('Landrun has modified or untracked sources')
    go = os.environ.get('GO', 'go')
    subprocess.run([go, 'build', '-o', str(cache/'landrun'), 'cmd/landrun/main.go'], cwd=landrun, check=True)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
executables = {'comparator': up/'.lake/build/bin/comparator',
               'lean4export': up/'.lake/packages/lean4export/.lake/build/bin/lean4export'}
provenance = {'lean_version': run('lean', '--version'),
    'executables': {k: sha(v) for k,v in executables.items()},
    'adapted_metadata': {f: sha(up/f) for f in sorted(allowed)},
    'official_lean_sources': {f: sha(up/f) for f in run('git', 'ls-files', '*.lean', cwd=up).splitlines()},
    'trusted_local_helper': sha(cache/'trusted-local-landrun')}
if (cache/'landrun').is_file():
    provenance['executables']['landrun'] = sha(cache/'landrun')
(cache/'build-provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
print('Official comparator and exporter built for Lean 4.19.0 in', cache)
PY
