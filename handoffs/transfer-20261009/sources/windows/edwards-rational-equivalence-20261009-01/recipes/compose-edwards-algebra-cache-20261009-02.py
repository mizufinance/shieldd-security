from pathlib import Path
import hashlib,json,os,subprocess,sys
cache=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-jubjub-isolated-05')
source=cache/'modules';stage=Path(sys.argv[1]).resolve()
expected=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-edwards-algebra-20261009-02-kernel/project').resolve()
assert stage==expected,'exact fresh diagnostic project required'
inspection=Path('C:/src/shieldd-transfer-handoffs/edwards-algebra-closure-inspection-20261009-02.json')
data=json.loads(inspection.read_text())
assert not data['missing'] and data['bytes']<1024**3
identities=json.loads((cache/'inputs.json').read_text())
package_root=Path('C:/src/shieldd-formal/circuits/.lake/packages')
for name,commit in identities['packages'].items():
    p=package_root/name
    assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==commit
    assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],text=True).strip()
for item in data['sources'].values():assert hashlib.sha256(Path(item['source']).read_bytes()).hexdigest()==item['sha256']
records=[]
for item in data['files']:
    p=Path(item['path']);relative=p.relative_to(source);target=stage/relative
    assert not target.exists()
    target.parent.mkdir(parents=True,exist_ok=True)
    digest=hashlib.sha256(p.read_bytes()).hexdigest()
    os.link(p,target)
    assert hashlib.sha256(target.read_bytes()).hexdigest()==digest
    records.append({'path':str(relative).replace('\\','/'),'sha256':digest})
receipt={'kind':'Read-only exact-source-closure diagnostic hardlink overlay; no theorem credit',
         'files':len(records),'source_modules':len(data['sources']),'bytes':data['bytes'],
         'inspection_sha256':hashlib.sha256(inspection.read_bytes()).hexdigest(),
         'identities_sha256':hashlib.sha256(json.dumps(records,sort_keys=True).encode()).hexdigest(),
         'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(stage.parent/'external-overlay.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
print(json.dumps(receipt))
