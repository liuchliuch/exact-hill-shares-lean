#!/usr/bin/env python3
"""Execute upstream comparator, retaining independent exports and active controls.

--trusted-local is for owned/reviewed source: the official upstream development
helper deliberately does not sandbox. --sandboxed requires Landlock and the
upstream-recommended systemd AF_UNIX restriction and never downgrades.
"""
import argparse
import ctypes
import datetime
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
p = argparse.ArgumentParser(description=__doc__)
modes = p.add_mutually_exclusive_group(required=True)
modes.add_argument('--trusted-local', action='store_true')
modes.add_argument('--sandboxed', action='store_true')
selection = p.add_mutually_exclusive_group()
selection.add_argument('--controls-only', action='store_true')
selection.add_argument('--paper-only', action='store_true')
a = p.parse_args()
CACHE = Path(os.environ.get('COMPARATOR_CACHE',
    str(Path(os.environ.get('XDG_CACHE_HOME', Path.home()/'.cache'))/
        'exact-hill-shares'/'comparator-lean4.19.0'))).resolve()
LOG = ROOT/'build'/'comparator'
WORK = ROOT/'.lake'/'comparator-work'
LOG.mkdir(parents=True, exist_ok=True)
WORK.mkdir(parents=True, exist_ok=True)
pins = json.loads((ROOT/'comparator'/'PINS.json').read_text())
source = CACHE/'source'
exe = source/'.lake'/'build'/'bin'/'comparator'
exporter = source/'.lake'/'packages'/'lean4export'/'.lake'/'build'/'bin'/'lean4export'
helper = CACHE/'trusted-local-landrun'

def command(argv, cwd=None):
    return subprocess.check_output([str(x) for x in argv], cwd=cwd, text=True).strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def source_hashes():
    paths = [ROOT/'ExactHillShares.lean', ROOT/'lakefile.lean', ROOT/'lean-toolchain', ROOT/'lake-manifest.json']
    for directory in ('ExactHillShares', 'Challenge', 'Solution'):
        paths.extend(x for x in (ROOT/directory).rglob('*') if x.is_file())
    paths.extend(ROOT/'comparator'/s for s in ('PINS.json','paper.json','controls.json'))
    paths.extend(ROOT/'scripts'/s for s in ('compare.sh', 'compare.py', 'bootstrap-comparator.sh'))
    return {str(x.relative_to(ROOT)): digest(x) for x in sorted(paths)}

def check_tools():
    require(exe.is_file() and exporter.is_file(),
            'Run scripts/bootstrap-comparator.sh first (same COMPARATOR_CACHE).')
    require('version 4.19.0,' in command(['lean', '--version']), 'Lean 4.19.0 is required.')
    for key, path in [('comparator', source), ('lean4export', source/'.lake'/'packages'/'lean4export'),
                      ('lean4checker', source/'.lake'/'packages'/'lean4checker')]:
        require(command(['git', 'rev-parse', 'HEAD'], path) == pins[key]['rev'], f'{key} revision mismatch')
        if key == 'comparator':
            # Toolchain/dependency metadata may differ only as required for 4.19.
            dirty = set(command(['git', 'diff', '--name-only', 'HEAD'], path).splitlines())
            require(not dirty-{'lean-toolchain','lakefile.toml','lake-manifest.json'},
                    'Official comparator source was modified.')
            require(not command(['git', 'ls-files', '--others', '--exclude-standard'], path),
                    'Unexpected untracked files in official comparator checkout.')
        else:
            require(not command(['git', 'status', '--porcelain', '--untracked-files=all'], path),
                    f'{key} sources were modified or untracked files were added.')
    expected_metadata = {'lean-toolchain': 'leanprover/lean4:v4.19.0\n',
        'lakefile.toml': (command(['git','show','HEAD:lakefile.toml'], source)+'\n').replace('v4.24.0','v4.19.0')}
    manifest = json.loads(command(['git','show','HEAD:lake-manifest.json'], source))
    for dep in manifest['packages']:
        dep['rev'] = pins[dep['name']]['rev']
        dep['inputRev'] = 'v4.19.0'
    expected_metadata['lake-manifest.json'] = json.dumps(manifest, indent=2)+'\n'
    for name, expected in expected_metadata.items():
        require((source/name).read_text() == expected, f'Unexpected adapted comparator metadata: {name}')
    provenance = json.loads((CACHE/'build-provenance.json').read_text())
    for name, path in [('comparator', exe), ('lean4export', exporter)]:
        require(digest(path) == provenance['executables'][name], f'{name} binary differs from bootstrap record.')
    require(provenance['lean_version'] == command(['lean','--version']), 'Toolchain differs from bootstrap record.')
    for name, expected in provenance['official_lean_sources'].items():
        require(digest(source/name) == expected, f'Official source differs from bootstrap record: {name}')
    (LOG/'tool-build-provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
    if a.trusted_local:
        require(helper.is_file() and digest(helper) == pins['trusted_local_helper']['sha256'],
                'Pinned official development helper is missing or modified.')
    else:
        require(sys.platform == 'linux' and os.uname().machine == 'x86_64',
                'Sandbox preflight currently supports Linux x86_64 only.')
        require(os.geteuid() != 0, 'Do not execute comparator as a privileged user.')
        libc = ctypes.CDLL(None, use_errno=True)
        abi = libc.syscall(444, 0, 0, 1)  # x86_64 landlock_create_ruleset(NULL, 0, VERSION)
        require(abi >= 6, f'Landlock ABI >= 6 required; got {abi}, errno {ctypes.get_errno()}. No fallback.')
        require((CACHE/'landrun').is_file(), 'Run bootstrap-comparator.sh --with-landrun first.')
        require(digest(CACHE/'landrun') == provenance['executables'].get('landrun'),
                'Landrun binary differs from bootstrap record.')
        require(shutil.which('systemd-run') is not None, 'systemd-run is required. No fallback.')
        subprocess.run(['systemd-run', '--user', '--wait', '--pipe',
                        '--property=RestrictAddressFamilies=~AF_UNIX', '--', 'true'], check=True)

results = []

def run_case(label, project, config, expected_success, diagnostic=None):
    out = LOG/label
    out.mkdir(parents=True, exist_ok=True)
    for previous_export in out.glob('*.ndjson'):
        previous_export.unlink()
    config_path = out/'config.json'
    config_path.write_text(json.dumps(config, indent=2)+'\n')
    bin_dir = WORK/'bin'/label
    bin_dir.mkdir(parents=True, exist_ok=True)
    landrun = helper if a.trusted_local else CACHE/'landrun'
    for name, target in [('landrun', landrun)]:
        link = bin_dir/name
        if link.is_symlink(): link.unlink()
        require(not link.exists(), f'Unexpected non-symlink at {link}')
        
        if name == 'landrun':
            link.symlink_to(ROOT/'scripts'/('local-landrun.sh' if a.trusted_local else 'landrun-runner.sh'))
        else:link.symlink_to(target)
    export_cmd = bin_dir/'lean4export'
    if a.trusted_local:
        if export_cmd.is_symlink():
            export_cmd.unlink()
        # This wrapper records exactly the stdout read by upstream Comparator.
        # It does not alter the exported NDJSON, and fails if either stage fails.
        export_cmd.write_text('#!/usr/bin/env bash\nset -euo pipefail\n'
            +'case "${1:-}" in '+shlex.quote(config['challenge_module'])+'|'+shlex.quote(config['solution_module'])
            +') ;; *) echo "Unexpected export module" >&2; exit 2;; esac\n'
            +shlex.quote(str(exporter))+' "$@" | tee '+shlex.quote(str(out))+'/"$1.ndjson"\n')
        export_cmd.chmod(0o755)
    else:
        if export_cmd.exists() or export_cmd.is_symlink(): export_cmd.unlink()
        export_cmd.symlink_to(exporter)
    env = dict(os.environ)
    env['PATH'] = str(bin_dir)+os.pathsep+env['PATH']
    env['LEAN_ABORT_ON_PANIC'] = '1'
    env['LEAN_NUM_THREADS']=os.environ.get('LEAN_NUM_THREADS','2')
    env['LANDRUN_EXECUTABLE']=str(CACHE/'landrun')
    argv = ['lake', 'env', str(exe), str(config_path)]
    if a.sandboxed:
        argv = ['systemd-run', '--user', '--wait', '--pipe',
                '--property=RestrictAddressFamilies=~AF_UNIX', '-E', 'PATH='+env['PATH'], '-E', 'LANDRUN_EXECUTABLE='+env['LANDRUN_EXECUTABLE'], '-E', 'LEAN_NUM_THREADS='+env['LEAN_NUM_THREADS'],
                '--working-directory='+str(project), '--']+argv
    print(f'COMPARATOR_BEGIN\t{label}', flush=True)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (out/'run.log').open('w') as log:
        completed = subprocess.run(argv, cwd=project, env=env, stdout=log, stderr=subprocess.STDOUT)
    text = (out/'run.log').read_text()
    success_marker = 'Your solution is okay!' in text and 'Lean default kernel accepts the solution' in text
    require('PANIC at' not in text and 'ASSERTION FAILED' not in text,
            f'{label}: panic; see {out / "run.log"}')
    if expected_success:
        require(completed.returncode == 0 and success_marker, f'{label}: comparator failed; see {out / "run.log"}')
    else:
        require(completed.returncode != 0 and not success_marker and diagnostic in text,
                f'{label}: expected specific rejection missing; see {out / "run.log"}')
    exports = {x.name: {'sha256': digest(x), 'bytes': x.stat().st_size}
               for x in sorted(out.glob('*.ndjson'))}
    if a.trusted_local:
        require(set(exports) == {config['challenge_module']+'.ndjson', config['solution_module']+'.ndjson'},
                f'{label}: both isolated exports were not captured')
    results.append({'name': label, 'expected_acceptance': expected_success,
        'exit_code': completed.returncode, 'passed': True, 'started': started,
        'theorem_names': config['theorem_names'], 'definition_names': config.get('definition_names', []),
        'rejection_diagnostic': diagnostic, 'exports': exports})
    print(f'COMPARATOR_PASS\t{label}\t'+('accepted + kernel replay' if expected_success else diagnostic), flush=True)

try:
    check_tools()
    before = source_hashes()
    (LOG/'source-hashes-before.json').write_text(json.dumps(before, indent=2)+'\n')
    (LOG/'tool-pins.json').write_text(json.dumps(pins, indent=2)+'\n')
    mode = 'trusted-local, no sandbox guarantee' if a.trusted_local else 'Landrun + systemd AF_UNIX restriction'
    print('COMPARATOR_MODE\t'+mode, flush=True)
    if not a.controls_only:
        config = json.loads((ROOT/'comparator'/'paper.json').read_text())
        require(config['challenge_module'] == 'Challenge.Expected' and
                config['solution_module'] == 'Solution.Proofs', 'Unexpected paper module selection.')
        expected_theorems = {'PaperContract.'+name for name in ('exact_share_formula',
            'simultaneous_guarantee', 'rational_allocator_correct', 'ordered_tail_domination',
            'feasible_interval_width')}
        require(len(config['theorem_names']) == 5 and set(config['theorem_names']) == expected_theorems,
                'Paper comparison must cover all five contracts.')
        require(config.get('definition_names') == ['PaperContract.allocate'],
                'Only the allocator implementation may be filled as a definition hole.')
        require(set(config['permitted_axioms']) == {'propext','Quot.sound','Classical.choice'},
                'Unexpected axiom whitelist.')
        require(config.get('enable_nanoda') is False, 'External kernel setup has not been configured.')
        run_case('paper', ROOT, config, True)
    if not a.paper_only:
        controls = json.loads((ROOT/'comparator'/'controls.json').read_text())
        project = WORK/'controls'
        project.mkdir(parents=True, exist_ok=True)
        (project/'lean-toolchain').write_text('leanprover/lean4:v4.19.0\n')
        (project/'lakefile.toml').write_text('name = "comparatorControls"\nversion = "0.1.0"\n'
            '[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Candidate"\n')
        (project/'Challenge.lean').write_text(controls['challenge'])
        for case in controls['cases']:
            (project/'Candidate.lean').write_text(case['source'])
            cfg = {'challenge_module':'Challenge', 'solution_module':'Candidate',
                   'theorem_names':['ComparatorControl.target'], 'definition_names':[],
                   'permitted_axioms':['propext','Quot.sound','Classical.choice'], 'enable_nanoda':False}
            run_case(case['name'], project, cfg, case['accept'], case.get('diagnostic'))
    require(before == source_hashes(), 'Sources changed during comparison; rerun after edits settle.')
    status = {'passed': True, 'mode': mode, 'external_kernel': False,
              'lean_version': command(['lean','--version']), 'results': results,
              'finished': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (LOG/'summary.json').write_text(json.dumps(status, indent=2)+'\n')
    print('COMPARATOR_SUITE_PASSED', flush=True)
except Exception as error:
    (LOG/'summary.json').write_text(json.dumps({'passed':False, 'results':results,
        'error':str(error)}, indent=2)+'\n')
    print('COMPARATOR_SUITE_FAILED: '+str(error), file=sys.stderr)
    sys.exit(1)
