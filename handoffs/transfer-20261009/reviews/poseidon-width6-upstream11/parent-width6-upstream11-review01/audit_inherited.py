"""Check exact stage copies and receipt ancestry; grant no fresh execution credit."""
import hashlib,json
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];S=R/'work/mac-poseidon-width6-upstream11'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records={}
for file,key in [('input-packet02.json','reused'),('import-extension01.json','imports')]:
    for name,x in json.loads((H/'frozen/inputs'/file).read_text())[key].items():
        if name in records:assert records[name]['source_sha256']==x['source_sha256'] and records[name]['object_sha256']==x['object_sha256']
        records[name]=x
checked=[]
for name,x in sorted(records.items()):
    if not (H/'frozen/project/ShielddSecurity'/(name+'.lean')).exists():continue
    source=S/'project/ShielddSecurity'/(name+'.lean');obj=S/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
    assert sha(source)==x['source_sha256'] and sha(obj)==x['object_sha256']
    current=R/'work/shared-build-handoff/circuits/ShielddSecurity'/source.name
    assert sha(current)==x['source_sha256']
    p=R/x['original_receipt_path'];assert sha(p)==x['original_receipt_sha256'];j=json.loads(p.read_text());seen=set();chain=[]
    while True:
        assert j['status']=='passed' and j['source_sha256']==x['source_sha256'] and j['object_sha256']==x['object_sha256']
        assert str(p) not in seen;seen.add(str(p));chain.append(str(p.relative_to(R)))
        if not j.get('reused_from_exact_pass_receipt'):break
        ancestor=j['reused_from_exact_pass_receipt'];p=R/ancestor['path'];assert sha(p)==ancestor['sha256'];j=json.loads(p.read_text())
    assert j['exit']==0
    checked.append({'module':name,'source_sha256':x['source_sha256'],'object_sha256':x['object_sha256'],'receipt_ancestry':chain,'fresh_credit':0})
result={'schema':'parent-upstream11-inherited-object-receipt-ancestry-v1','exact_inherited_source_object_canonical_matches':len(checked),'checks':checked,'scope':'inherited sources required by frozen169-module owned root closure; unused stage copies excluded','initial_inspection_refusal':'unused diagnostic copiedmodule lacked canonicalpublication; narrow ownedclosure selected before retry','fresh_execution_credit':0,'parent_kernel_runs':0,'full_transfer':'OPEN'}
p=H/'inherited-audit01.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='checks'}))
