#!/usr/bin/env bash
# Compile the complete proof/test/solution inventory, audit all local origins,
# and replay safe stored declarations through Lean's kernel.
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT"
if [[ -n ${LEAN_HOME:-} ]]; then export PATH="$LEAN_HOME/bin:$PATH"; fi
command -v lake >/dev/null || { echo 'Use elan or scripts/with-toolchain.sh.' >&2; exit 2; }
MODE=(--safe-declarations)
if [[ ${1:-} == --replay-all ]]; then MODE+=(--replay-all); shift; fi
if [[ $# != 0 ]]; then echo 'Usage: scripts/validate.sh [--replay-all]' >&2; exit 2; fi
LOG=${AUDIT_LOG_DIR:-"$ROOT/build/validation"}
mkdir -p "$LOG" "$ROOT/.lake/audit"
FRESH=$(mktemp -d "$ROOT/.lake/audit/fresh.XXXXXX")
export AUDIT_LOG_DIR="$LOG"
printf '{"status":"running"}\n' > "$LOG/summary.json"
date -u +'%Y-%m-%dT%H:%M:%SZ' > "$LOG/start-time.txt"
lean --version | tee "$LOG/lean-version.txt"
lake --version > "$LOG/lake-version.txt"
grep -q 'version 4.19.0,' "$LOG/lean-version.txt"

python3 scripts/proof-sources.py > "$LOG/sources.tsv"
cut -f1 "$LOG/sources.tsv" > "$LOG/modules.txt"
MODULES=()
while IFS= read -r module; do MODULES+=("$module"); done < "$LOG/modules.txt"
python3 scripts/scan-proof-sources.py --manifest "$LOG/sources.tsv" \
  | tee "$LOG/source-policy-scan.log"
python3 - "$LOG" <<'PY'
import hashlib, json, pathlib, platform, subprocess, sys
log = pathlib.Path(sys.argv[1])
def hashes(paths):
    return ''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.as_posix()}\n' for p in paths)
sources = [pathlib.Path(row.split('\t')[1]) for row in (log/'sources.tsv').read_text().splitlines()]
controls = [pathlib.Path('scripts')/name for name in (
    'AuditOrigins.lean','validate.sh','audit-negative-tests.sh',
    'scan-proof-sources.py','proof-sources.py')]
controls += [pathlib.Path(p) for p in ('lakefile.lean','lean-toolchain','lake-manifest.json')]
(log/'source-hashes.sha256').write_text(hashes(sources))
(log/'control-hashes.sha256').write_text(hashes(controls))
manifest = json.loads(pathlib.Path('lake-manifest.json').read_text())
deps = []
for package in manifest['packages']:
    path = pathlib.Path(manifest['packagesDir']) / package['name']
    def git(*args):
        return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()
    if git('rev-parse', 'HEAD') != package['rev'] or git('status', '--porcelain', '--untracked-files=no'):
        raise SystemExit(f"Dependency is unpinned or has changed tracked files: {package['name']}")
    deps.append({'name': package['name'], 'revision': package['rev']})
prefix = pathlib.Path(subprocess.check_output(['lean','--print-prefix'], text=True).strip())
binaries = [prefix/'bin/lean', prefix/'bin/lake'] + sorted((prefix/'lib/lean').glob('libleanshared*'))
binary_hashes = {p.relative_to(prefix).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in binaries if p.is_file()}
(log/'toolchain.json').write_text(json.dumps({
    'lean': (log/'lean-version.txt').read_text().strip(),
    'lake': (log/'lake-version.txt').read_text().strip(),
    'platform': platform.system(), 'architecture': platform.machine(),
    'binary_sha256': binary_hashes,
    'dependencies': deps}, indent=2)+'\n')
PY
lake build "${MODULES[@]}" > "$LOG/lake-build.log" 2>&1 || {
  tail -40 "$LOG/lake-build.log" >&2; exit 1;
}
printf 'LAKE_BUILD_PASSED\t%s modules\n' "${#MODULES[@]}"

# Every local import resolves to an independently rebuilt object in this unique
# directory. The Lake build is a separate check, never the fresh-source evidence.
BASE_PATH=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$FRESH:$BASE_PATH"
: > "$LOG/fresh-source-check.log"
while IFS=$'\t' read -r module source; do
  target="$FRESH/${module//.//}.olean"
  mkdir -p "$(dirname "$target")"
  printf 'FRESH_SOURCE_CHECK\t%s\n' "$module" | tee -a "$LOG/fresh-source-check.log"
  lean -t 0 -o "$target" "$source" >> "$LOG/fresh-source-check.log" 2>&1 || {
    tail -40 "$LOG/fresh-source-check.log" >&2; exit 1;
  }
done < "$LOG/sources.tsv"
if grep -E '(^|[[:space:]])PANIC at|ASSERTION FAILED' \
    "$LOG/lake-build.log" "$LOG/fresh-source-check.log"; then
  echo 'Build or regression emitted a runtime panic.' >&2; exit 1
fi

# A malformed imported object can pass -t0 in Lean 4.19. Actual kernel replay
# is a separate step; --replay-all begins from an empty kernel environment.
printf 'ORIGIN_AND_KERNEL_AUDIT_BEGIN\n'
lean -t 0 --run scripts/AuditOrigins.lean -- "${MODE[@]}" "${MODULES[@]}" \
  > "$LOG/origin-axiom-kernel-audit.tsv" 2> "$LOG/origin-axiom-kernel-audit.err" || {
    tail -20 "$LOG/origin-axiom-kernel-audit.err" >&2; exit 1;
  }
if grep -Ei '(^|[[:space:]])PANIC at|ASSERTION FAILED' \
    "$LOG/origin-axiom-kernel-audit.tsv" "$LOG/origin-axiom-kernel-audit.err"; then
  echo 'Kernel replay emitted a runtime panic.' >&2; exit 1
fi
tail -1 "$LOG/origin-axiom-kernel-audit.tsv"
scripts/audit-negative-tests.sh > "$LOG/negative-tests.txt" 2>&1 || {
  cat "$LOG/negative-tests.txt" >&2; exit 1;
}
tail -1 "$LOG/negative-tests.txt"
python3 - "$LOG" <<'PYHASH'
import hashlib, pathlib, sys
log = pathlib.Path(sys.argv[1])
for category in ('source', 'control'):
    checked = []
    for line in (log/f'{category}-hashes.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        if hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f'File changed during validation: {name}')
        checked.append(f'{name}: OK\n')
    (log/f'{category}-stability.log').write_text(''.join(checked))
PYHASH
python3 scripts/proof-sources.py > "$LOG/sources-after.tsv"
cmp "$LOG/sources.tsv" "$LOG/sources-after.tsv"
date -u +'%Y-%m-%dT%H:%M:%SZ' > "$LOG/end-time.txt"
python3 - "$LOG" "$FRESH" <<'PY'
import collections, hashlib, json, pathlib, subprocess, sys
log, fresh = map(pathlib.Path, sys.argv[1:])
lines = (log/'origin-axiom-kernel-audit.tsv').read_text().splitlines()
modules = set((log/'modules.txt').read_text().splitlines())
rows = [line.split('\t', 4) for line in lines
        if line.split('\t', 1)[0] in modules and len(line.split('\t', 4)) == 5]
header = 'module\tdeclaration\tkind\tsafety\tnew_axioms_in_safety_class_union\n'
(log/'origin-inventory.tsv').write_text(header+''.join('\t'.join(row)+'\n' for row in rows))
(log/'excluded-compiler-artifacts.tsv').write_text(header+''.join(
    '\t'.join(row)+'\n' for row in rows if row[3] in {'unsafe','partial'}))
metadata = [line for line in lines if line.startswith('COMPILER_NAME_METADATA_ONLY\t')]
(log/'compiler-name-metadata-only.tsv').write_text('\n'.join(metadata)+'\n')
fields = dict(line.split('\t', 1) for line in lines if '\t' in line)
replay = dict(item.split('=', 1) for item in fields['KERNEL_REPLAY_BEGIN'].split('\t'))
if 'KERNEL_REPLAY_PASSED' not in lines or not any(line.startswith('AXIOM_AUDIT_PASSED\t') for line in lines):
    raise SystemExit('Required audit pass markers missing')
# Pin checks are repeated after all source and replay work.
toolchain = json.loads((log/'toolchain.json').read_text())
prefix = pathlib.Path(subprocess.check_output(['lean','--print-prefix'], text=True).strip())
for relative, digest in toolchain['binary_sha256'].items():
    if hashlib.sha256((prefix/relative).read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Toolchain binary changed during validation: {relative}')
for dependency in toolchain['dependencies']:
    path = pathlib.Path('.lake/packages')/dependency['name']
    def git(*args):
        return subprocess.check_output(['git','-C',str(path),*args], text=True).strip()
    if git('rev-parse','HEAD') != dependency['revision'] or git('status','--porcelain','--untracked-files=no'):
        raise SystemExit(f"Dependency changed during validation: {dependency['name']}")
(log/'fresh-object-hashes.sha256').write_text(''.join(
    f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(fresh).as_posix()}\n'
    for p in sorted(fresh.rglob('*.olean'))))
summary = {
    'status': 'passed',
    'started_utc': (log/'start-time.txt').read_text().strip(),
    'finished_utc': (log/'end-time.txt').read_text().strip(),
    'source_modules': len(modules),
    'source_policy': 'all production, regression, challenge definitions, and solution sources',
    'excluded_specification': 'Challenge/Expected.lean (untrusted comparator placeholders)',
    'origin_declarations': len(rows),
    'kinds': dict(sorted(collections.Counter(row[2] for row in rows).items())),
    'safety': dict(sorted(collections.Counter(row[3] for row in rows).items())),
    'compiler_name_metadata_only': len(metadata),
    'imported_modules': int(fields['IMPORTED_MODULE_COUNT']),
    'safe_transitive_axiom_union': fields['SAFE_TRANSITIVE_AXIOM_UNION'],
    'unsafe_nonfoundational_axioms': int(fields['UNSAFE_NONFOUNDATIONAL_AXIOM_COUNT']),
    'kernel_replay': {
        'mode': replay['mode'],
        'stored_declarations': int(replay['declarations']),
        'unsafe_or_partial_skipped': int(replay['unsafe-or-partial-skipped']),
        'safe_nonpartial_replayed': int(replay['declarations'])-int(replay['unsafe-or-partial-skipped']),
        'declaration_bearing_modules': sum(line.startswith('KERNEL_MODULE_REPLAYED\t') for line in lines),
        'passed': True},
    'negative_controls': 7,
    'positive_comment_string_control': True,
    'source_and_control_stability': True,
    'scope_note': 'Logical validation and structural cost proofs; not compiler correctness or bit complexity.'}
(log/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
print(f"VALIDATION_PASSED: {len(modules)} source modules; {len(rows)} originating declarations; "
      f"{summary['kernel_replay']['safe_nonpartial_replayed']} safe/nonpartial constants replayed.")
print('Evidence: build/validation (or AUDIT_LOG_DIR when overridden).')
PY
