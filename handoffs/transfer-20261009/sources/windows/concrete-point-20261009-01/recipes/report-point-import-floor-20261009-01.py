from pathlib import Path
import hashlib,json
local=Path('C:/src/shieldd-transfer-handoffs')
p=local/'edwards-point-closure-inspection-20261009-01.json'
data=json.loads(p.read_text());counts={};missing={}
def suffix(path):
    for part in ['.olean.private','.olean.server','.olean','.ir']:
        if path.endswith(part):return part
    raise ValueError(path)
for item in data['files']:
    part=suffix(item['path']);record=counts.setdefault(part,{'files':0,'bytes':0})
    record['files']+=1;record['bytes']+=item['bytes']
for path in data['missing']:
    part=suffix(path);missing[part]=missing.get(part,0)+1
toolchain=Path('C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Lean')
result={'kind':'Source-backed batch-import floor; no proof credit','modules':len(data['sources']),
 'present_artifacts_by_type':counts,'missing_by_type':missing,'present_byte_floor':sum(x['bytes'] for x in counts.values()),'limit_bytes':1024**3,
 'source_identity':{'inspection':hashlib.sha256(p.read_bytes()).hexdigest(),**{name:hashlib.sha256((toolchain/name).read_bytes()).hexdigest() for name in ['Environment.lean','Setup.lean','Elab/Frontend.lean']}},
 'plain_legacy_batch_rules':{
   'globalLevel':'private for non-module proof sources',
   'Environment.lean:2124-2128':'globalLevel private sets importAll true transitively; needsIR true for all imported modules',
   'Environment.lean:2038-2051':'private compacted region is loaded after server region; neither can be independently discarded',
   'Setup.lean:92-104':'server companion is required when private companion supplied, even outside server mode'},
 'disposition':'Existing legacy batch lane requires exported/server/private/IR closure. Present mandatory artifacts already exceed cap; missing artifacts only increase floor. No thin Point stage or Point credit.',
 'strict_module_alternative':'Could use exported-only module-specific artifacts for standalone Point floor; cannot import established non-module Group/Equiv sources, so not a demonstrated full join. No module migration or budget changes.'}
out=local/'point-import-floor-report-20261009-01.json';assert not out.exists()
out.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps(result))
