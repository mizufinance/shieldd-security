from pathlib import Path
import hashlib,json,shutil,subprocess
local=Path('C:/src/shieldd-transfer-handoffs')
data=json.loads((local/'edwards-point-closure-inspection-20261009-01.json').read_text())
packages=Path('C:/src/shieldd-formal/circuits/.lake/packages')
records=[]
for raw in data['missing']:
    relative=Path(raw).relative_to(Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-jubjub-isolated-05/modules'))
    assert relative.parts[0]=='Mathlib',relative
    choices=[packages/'mathlib/.lake/build/lib/lean'/relative]
    existing=[p for p in choices if p.exists()]
    assert len(existing)<=1,(relative,existing)
    records.append({'relative':relative.as_posix(),'available':bool(existing),
       **({'path':str(existing[0]),'bytes':existing[0].stat().st_size,'sha256':hashlib.sha256(existing[0].read_bytes()).hexdigest()} if existing else {})})
git=lambda *args:subprocess.check_output(['git','-C',str(packages/'mathlib'),*args],text=True).strip()
assert git('rev-parse','HEAD')=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
assert not git('status','--porcelain','--untracked-files=no')
free=shutil.disk_usage('C:/src').free
result={'kind':'Read-only exact-source artifact availability, no import/proof credit','records':records,
 'available':sum(v['available'] for v in records),'missing':sum(not v['available'] for v in records),
 'additional_available_bytes':sum(v.get('bytes',0) for v in records),'present_floor_bytes':data['bytes'],
 'complete_if_available':all(v['available'] for v in records),'disk_free_bytes':free,'mathlib_commit':git('rev-parse','HEAD')}
out=local/'point-official-artifact-inspection-20261009-01.json';assert not out.exists();out.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({k:v for k,v in result.items() if k!='records'}))
