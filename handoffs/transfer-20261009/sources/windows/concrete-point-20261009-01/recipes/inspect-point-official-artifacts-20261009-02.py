from pathlib import Path
import hashlib,json,subprocess,shutil
local=Path('/mnt/c/src/shieldd-transfer-handoffs')
data=json.loads((local/'edwards-point-closure-inspection-20261009-01.json').read_text())
root=Path('/root/.cache/shieldd-security-verification/b0f7e8b/circuits/.lake/packages')
cache=Path('/mnt/c/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-jubjub-isolated-05/modules')
records=[];identities={}
for name,rev in json.loads((cache.parent/'inputs.json').read_text())['packages'].items():
    p=root/name
    current=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip();assert current==rev
    assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],text=True).strip()
    identities[name]=current
for name,item in data['sources'].items():
    source=Path(name.replace('.','/')+'.lean')
    matches=[p/source for p in root.iterdir() if (p/source).is_file()]
    assert len(matches)==1,(name,matches)
    assert hashlib.sha256(matches[0].read_bytes()).hexdigest()==item['sha256'],name
for raw in data['missing']:
    relative=Path(raw.replace('\\','/').split('/modules/',1)[1])
    matches=[p/'.lake/build/lib/lean'/relative for p in root.iterdir() if (p/'.lake/build/lib/lean'/relative).is_file()]
    assert len(matches)<=1,(relative,matches)
    records.append({'relative':relative.as_posix(),'available':bool(matches),
      **({'path':str(matches[0]),'bytes':matches[0].stat().st_size,'sha256':hashlib.sha256(matches[0].read_bytes()).hexdigest()} if matches else {})})
result={'kind':'Read-only pinned official-cache artifact qualification, no import/proof credit','records':records,'packages':identities,
 'available':sum(v['available'] for v in records),'missing':sum(not v['available'] for v in records),
 'additional_bytes':sum(v.get('bytes',0) for v in records),'present_floor_bytes':data['bytes'],
 'projected_final_bytes':data['bytes']+sum(v.get('bytes',0) for v in records),'limit_bytes':2*1024**3,
 'disk_free_bytes':shutil.disk_usage('/mnt/c/src').free,'complete':all(v['available'] for v in records),
 'inspection_sha256':hashlib.sha256((local/'edwards-point-closure-inspection-20261009-01.json').read_bytes()).hexdigest()}
out=local/'point-official-artifact-inspection-20261009-02.json';assert not out.exists();out.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({k:v for k,v in result.items() if k not in ['records','packages']}))
