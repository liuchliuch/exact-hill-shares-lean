#!/usr/bin/env python3
"""Cleanly compile the complete fixed library and run its retained checks."""
import argparse,hashlib,json,os,re,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def output(cmd):return subprocess.check_output(cmd,cwd=ROOT,text=True).strip()
def run(cmd,log):
    print('+ '+' '.join(cmd),flush=True)
    with log.open('w') as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
    if p.returncode:print('\n'.join(log.read_text().splitlines()[-40:]),flush=True)
    require(p.returncode==0,'Check failed: '+str(log))
    require('PANIC at' not in log.read_text() and 'ASSERTION FAILED' not in log.read_text(),'Runtime failure: '+str(log))
def check_inputs():
    p=json.loads((ROOT/'verification/project.json').read_text())
    original=json.loads((ROOT/'verification/library-provenance.json').read_text())['sources']
    actual={x.relative_to(ROOT).as_posix() for x in (ROOT/p['library']).rglob('*.lean')}|{p['library']+'.lean'}
    require(actual <= set(original),'Unrecorded mathematical source')
    for name,digest in original.items():require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,'Fixed mathematical input changed: '+name)
    require((ROOT/'lean-toolchain').read_text().strip()==p['lean'],'Toolchain identity changed')
    require(output(['lean','-V'])==p['lean'].split(':v')[1],'Wrong active Lean version')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    for d in manifest['packages']:
        path=ROOT/manifest['packagesDir']/d['name']
        require(output(['git','-C',str(path),'rev-parse','HEAD'])==d['rev'],'Wrong dependency pin: '+d['name'])
        require(not output(['git','-C',str(path),'status','--porcelain','--untracked-files=no']),'Modified dependency: '+d['name'])
    return p
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--no-clean',action='store_true');a=parser.parse_args()
    os.chdir(ROOT);p=check_inputs();before=output([sys.executable,'scripts/snapshot.py'])
    logs=ROOT/'.lake/publication-results';logs.mkdir(parents=True,exist_ok=True)
    (logs/'result.json').write_text(json.dumps({'status':'RUNNING'})+'\n')
    if not a.no_clean:shutil.rmtree(ROOT/'.lake/build',ignore_errors=True)
    targets=[x.removesuffix('.lean').replace('/','.') for x in p['proof_files']]
    if (ROOT/'StatementContracts/Solution.lean').exists():targets+=['StatementContracts.Solution']
    run(['lake','build',*targets],logs/'build.log')
    if p['library']=='ExactHillShares':
        envlog=os.environ.get('AUDIT_LOG_DIR');os.environ['AUDIT_LOG_DIR']=str(logs/'hill-validation')
        run(['bash','scripts/validate.sh','--replay-all'],logs/'library-audit.log')
    else:
        run(['lake','env','lean','--trust=0','scripts/AuditOrigins.lean'],logs/'library-audit.log')
        require('PROJECT_AXIOM_AUDIT_PASS' in (logs/'library-audit.log').read_text(),'Missing complete axiom audit')
    if p['library']=='RankwidthDomination':
        run(['lake','env','lean','scripts/KernelReplay.lean'],logs/'kernel-replay.log')
        run(['lake','env','lean','scripts/EndpointSignatures.lean'],logs/'endpoint-signatures.log')
        run([sys.executable,'scripts/comparator-coverage-test.py','--project','.'],logs/'coverage.log')
    elif p['library']=='IndependentSetDiscovery':
        run([sys.executable,'scripts/generate_imports.py','--check'],logs/'aggregate-inventory.log')
        for f in sorted((ROOT/'Tests').glob('*.lean')):run(['lake','env','lean','--run',str(f)],logs/(f.stem+'.log'))
        for f in sorted((ROOT/'scripts').glob('Smoke*.lean')):run(['lake','env','lean',str(f)],logs/(f.stem+'.log'))
        run(['lake','env','lean','scripts/release_audit.lean'],logs/'body-recheck.log')
    elif p['library']=='GaussianPCA':
        run(['lake','env','lean','tests/BinomialRank.lean'],logs/'regressions.log')
        run(['lake','env','lean','scripts/release_audit.lean'],logs/'body-recheck.log')
    check_inputs();require(output([sys.executable,'scripts/snapshot.py'])==before,'Verification inputs changed during checks')
    result={'status':'PASS','source_snapshot':hashlib.sha256((before+'\n').encode()).hexdigest(),'clean_project_build':not a.no_clean,'proof_modules':len(p['proof_files']),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'kernel':'Pinned Lean default kernel'}
    (logs/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
