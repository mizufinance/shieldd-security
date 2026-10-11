from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;P=J/'packet01';R=J.parent/'windows-sdk-raw-auth-review01';B=R/'packet01'
def sha(b):return hashlib.sha256(b).hexdigest()
def pincheck(b,p):assert len(b)==p['bytes']and sha(b)==p['sha256']
M=json.loads((P/'manifest.json').read_bytes())
for p in M['files']:pincheck((P/p['path']).read_bytes(),p)
pincheck((B/'manifest.json').read_bytes(),M['parent_manifest'])
pincheck((R/'transport01.tar.xz').read_bytes(),M['parent_packet'])
a=json.loads((P/'coordinateBytes-full-audit.json').read_bytes());name=a['declaration']
assert name==M['declaration']=='ShielddSecurity.GroupNativeSdk.coordinateBytes'
assert sha(a['full_type'].encode())==a['full_type_sha256']
assert a['axioms']==['propext','Classical.choice','Quot.sound']
raw=(a['full_type']+"\n'"+name+"' "+a['axiom_report']+'\n').encode()
pincheck(raw,a['captured_stdout'])
receipt=a['receipt'];assert receipt['status']=='passed'and receipt['stdout']==a['captured_stdout']
assert receipt['audits'][name]=={k:a[k]for k in ['axioms','full_type_sha256']}
assert all(not line.strip()or line[0].isspace()for line in a['full_type'].splitlines()[1:])
assert not re.search(r'\b(?:warning|error|info|trace):|sorryAx',raw.decode())
source=(P/'handwritten-source/SDKCoordinateBytesAudit01.lean').read_bytes()
pincheck(source,a['qualified_diagnostic_source'])
assert re.findall(r'(?m)^import ([\w.]+)',source.decode())==['ShielddSecurity.GroupNativeSdk']
assert re.findall(r'(?m)^#check @([\w.]+)',source.decode())==[name]
retained=(P/'retained-source/GroupNativeSdk.lean').read_bytes()
assert retained==(B/'handwritten-source/ShielddSecurity/GroupNativeSdk.lean').read_bytes()
pincheck(retained,a['retained_sdk_source'])
prior=next(x for x in json.loads((R/'audit-result01.json').read_bytes())['modules']if x['module']=='GroupNativeSdk')
association=json.loads((P/'execution-context/retained-sdk-association.json').read_bytes())['retained']
assert association['receipt']==prior['receipt']
for k,v in [('source',a['retained_sdk_source']),('object',a['retained_sdk_object']),('copy',a['retained_first_package_copy'])]:assert association[k]==v
assert a['retained_sdk_object']in prior['receipt']['objects']
pool=json.loads((next(p for p in (B/'owned-import-context').rglob('composition-review.json')if sha(p.read_bytes())=='653a3c0cc0c61a12e9ae31f2a66895863a36694643231c78747eb87350842f73')).read_bytes())
pool_selected=next(x for x in pool['selected']if x['module']=='GroupNativeSdk')
assert pool_selected==association
plan=json.loads((P/'execution-context/plan.json').read_bytes())
assert pool_selected['copy']in plan['owned_imports']
assert pool_selected['copy']['path']==plan['lean_path'][0]+'\\ShielddSecurity\\GroupNativeSdk.olean'
assert plan['targets'][0]['audit_names']==[name]and plan['targets'][0]['source']==a['qualified_diagnostic_source']
runner=(P/'execution-context/execute_bounded.py').read_bytes()
assert sha(runner)=='7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
assert plan['limits']['heap_mib']==1536 and plan['limits']['threads']==1
assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
inventory=json.loads((R/'declaration-inventory01.json').read_bytes())
reports=[n for x in inventory['explicit_public_inventory']for n in x['reported_declarations']]+[name]
public=[n for x in inventory['explicit_public_inventory']for n in x['explicit_public_declarations']]
assert len(reports)==len(set(reports))==len(public)==173 and set(public)==set(reports)
result={'kind':'Exact supplemental original diagnostic reconstructed, source/object/import/guard associations matched against immutable base packet; no parent Lean replay','base_declarations':172,'additional_declarations':1,'public_inventory_complete':173,'manifest_pins':len(M['files']),'audit':a,'parent_manifest':M['parent_manifest'],'guard_byte_identical':True,'retained_source_object_unchanged':True,'full_transfer':'OPEN'}
with(J/'supplement-review01.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({k:result[k]for k in ['base_declarations','additional_declarations','public_inventory_complete','manifest_pins']}))
