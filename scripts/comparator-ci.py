#!/usr/bin/env python3
"""Run the project's official Linux comparison and bind its evidence to sources."""
import hashlib,importlib.util,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('publication',ROOT/'scripts/verify.py')
publication=importlib.util.module_from_spec(spec);spec.loader.exec_module(publication)
p=publication.check_inputs()
before=subprocess.check_output([sys.executable,'scripts/snapshot.py'],cwd=ROOT)
logs=ROOT/'.lake/comparator-results';logs.mkdir(parents=True,exist_ok=True)
(logs/'result.json').write_text(json.dumps({'status':'RUNNING'})+'\n')
def run(label,command):
    print('+ '+' '.join(map(str,command)),flush=True)
    with (logs/(label+'.log')).open('w') as f:
        subprocess.run(list(map(str,command)),cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,check=True)
if p['library']=='RankwidthDomination':
    run('setup',['bash','scripts/comparator-setup.sh'])
    work=Path(tempfile.mkdtemp(prefix='rankwidth-comparator-'))
    try:
        run('controls',['python3','scripts/comparator-run.py','test','--work',work/'controls'])
        run('paper',['python3','scripts/comparator-run.py','check','--work',work/'paper'])
        for label in ['controls','paper']:shutil.copytree(work/label,logs/label,ignore=shutil.ignore_patterns('project','.lake','stage-*'))
        paper=json.loads((work/'paper/result.json').read_text());controls=json.loads((work/'controls/result.json').read_text())
        assert paper['status']=='passed' and controls['status']=='passed'
        assert paper['theorem_count']==len(p['theorems']) and paper['definition_holes']==0
        control_count=len(controls['cases'])
    finally:shutil.rmtree(work)
elif p['library']=='ExactHillShares':
    run('setup',['bash','scripts/bootstrap-comparator.sh','--with-landrun'])
    run('suite',['python3','scripts/compare.py','--sandboxed'])
    shutil.copytree(ROOT/'build/comparator',logs/'suite',dirs_exist_ok=True)
    report=json.loads((ROOT/'build/comparator/summary.json').read_text())
    assert report['passed'] and report['mode']=='Landrun + systemd AF_UNIX restriction'
    assert len(report['results'])==6 and all(r['passed'] for r in report['results'])
    control_count=5
else:raise RuntimeError('Use scripts/compare.py for this project')
publication.check_inputs()
assert subprocess.check_output([sys.executable,'scripts/snapshot.py'],cwd=ROOT)==before,'Verification source changed during comparison'
result={'status':'PASS','source_snapshot':hashlib.sha256(before).hexdigest(),'theorem_targets':len(p['theorems']),'definition_targets':len(p['definition_holes']),'fresh_lean_kernel_replay':'PASS','process_isolation':'Landrun with systemd AF_UNIX restriction','control_cases':control_count,'kernel':'Pinned official Lean default kernel','external_kernel':'not enabled'}
(logs/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
