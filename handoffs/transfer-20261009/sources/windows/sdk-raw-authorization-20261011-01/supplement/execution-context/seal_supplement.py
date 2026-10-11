"""Seal one exact retained-object diagnostic without changing its parent packet."""
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
def pin(path):
    path=Path(path)
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
plan=json.loads((ROOT/'plan.json').read_text())
events=[json.loads(line) for line in (ROOT/'events.jsonl').read_text().splitlines()]
passes=[e for e in events if e['event']=='attempt_finished' and e['result']['status']=='passed']
assert len(passes)==1
result=passes[0]['result']
name='ShielddSecurity.GroupNativeSdk.coordinateBytes'
assert list(result['audits'])==[name]
assert set(result['audits'][name]['axioms']) <= {'propext','Classical.choice','Quot.sound'}
for r in [plan['targets'][0]['source'],result['stdout']]+result['objects']:
    assert pin(r['path'])==r
stdout=Path(result['stdout']['path']).read_bytes().decode('utf-8')
assert not re.search(r'\b(?:error|warning|info|trace):|\bsorryAx\b',stdout)
signature=stdout.split("\n'"+name+"' ",1)[0]
assert hashlib.sha256(signature.encode()).hexdigest()==result['audits'][name]['full_type_sha256']
parent=DIAG/'transfer-sdk-raw-authorization-endpoint-20261010-01'
parent_archive=pin(parent/'portable-windows-sdk-raw-authorization-endpoint01.tar.xz')
assert parent_archive['sha256']=='9476acbc0a844c582a7de1fe06085e1cadd54151e308c7cec1375a0669148918'
packet=ROOT/'supplement';packet.mkdir(exist_ok=False)
def copy(path,relative):
    path=Path(path); target=packet/relative
    target.parent.mkdir(parents=True,exist_ok=True)
    assert not target.exists()
    shutil.copyfile(path,target)
    assert pin(path)['sha256']==pin(target)['sha256']
copy(plan['targets'][0]['source']['path'],'handwritten-source/SDKCoordinateBytesAudit01.lean')
for filename in ['prepare.py','prepare_stage.py','execute_bounded.py','plan.json','review.json','events.jsonl','retained-sdk-association.json','seal_supplement.py']:
    copy(ROOT/filename,'execution-context/'+filename)
association=json.loads((ROOT/'retained-sdk-association.json').read_text())
copy(association['retained']['source']['path'],'retained-source/GroupNativeSdk.lean')
report={'declaration':name,'full_type':signature,**result['audits'][name],
        'axiom_report':stdout.split("\n'"+name+"' ",1)[1].strip(),
        'captured_stdout':result['stdout'],'receipt':result,
        'qualified_diagnostic_source':plan['targets'][0]['source'],
        'retained_sdk_source':association['retained']['source'],
        'retained_sdk_object':association['retained']['object'],
        'retained_first_package_copy':association['retained']['copy']}
(packet/'coordinateBytes-full-audit.json').write_text(json.dumps(report,indent=2)+'\n')
check=ROOT/'preservation_check.py'
shutil.copyfile(DIAG/'transfer-sdk-raw-authorization-checkpoint-20261010-01/preservation_check.py',check)
assert pin(check)['sha256']=='a1335795d4ffaf7e3ec797ea044fa424c13ddfcb8b7c117a612a7e221be37e74'
import subprocess
subprocess.run(['C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe',str(check)],check=True,capture_output=True)
for filename in ['preservation_check.py','preservation.json']:
    copy(ROOT/filename,'preservation/'+filename)
files=[]
for path in sorted(packet.rglob('*')):
    if path.is_file():
        r=pin(path);r['path']=path.relative_to(packet).as_posix();files.append(r)
manifest={'kind':'RETAINED_SDK_COORDINATE_BYTES_AUDIT_SUPPLEMENT','files':files,
          'declaration':name,'additional_type_axiom_pairs':1,'parent_packet':parent_archive,
          'parent_manifest':pin(parent/'packet/manifest.json'),
          'retained_sdk_source_sha256':association['retained']['source']['sha256'],
          'retained_sdk_object_sha256':association['retained']['object']['sha256'],
          'scope':'One omitted public definition report; exact retained SDK source/object unchanged. Parent16-source/172-report packet remains sealed. Global primitive correspondence, full circuit/runtime replay and Transfer certification remain OPEN.',
          'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
          'physical_guard_changes':False,'runtime_test_credit':0,'semantic_negative_control_credit':0,
          'native_source_correspondence_credit':0,'full_transfer':'OPEN','certification':False}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-coordinate-bytes-audit-supplement01.tar.xz'
with tarfile.open(archive,'w:xz',preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data=path.read_bytes();info=tarfile.TarInfo(path.relative_to(packet).as_posix());info.size=len(data);info.mtime=0;info.mode=0o644
            tar.addfile(info,io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128*1024**2
print(json.dumps({'archive':pin(archive),'manifest':pin(packet/'manifest.json'),'additional_audits':1,'retained_sdk_unchanged':True,'certification':False}))
