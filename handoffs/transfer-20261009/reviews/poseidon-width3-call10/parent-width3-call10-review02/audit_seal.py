"""Rehash finite sealed source/import packet and header-only successor, no builds."""
import hashlib,json,re
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];S=ROOT/'work/mac-poseidon-width3-call10';O=ROOT/'outputs/mac-poseidon-width3-call10';REPO=ROOT/'work/shared-build-handoff'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mp=O/'publication-manifest01.json';assert sha(mp)=='cd000d8c2a82560c081d2387aa06fb1a20481fc0684ea30352464637de3e15e9';m=json.loads(mp.read_text())
for x in m['files']:
    p=ROOT/x['path'];assert p.resolve().is_relative_to(ROOT.resolve())
    assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'],str(p)
canonical=0
for name,x in m['inherited_imports'].items():
    src=ROOT/x['source_path'];assert sha(src)==x['source_sha256']
    assert sha(ROOT/x['original_receipt_path'])==x['original_receipt_sha256']
    obj=S/'project/.lake/build/lib/lean'/Path(*name.split('.')).with_suffix('.olean')
    assert sha(obj)==x['object_sha256'],name
    key=name.split('.')[-1];canon=REPO/'circuits/ShielddSecurity'/(key+'.lean')
    if canon.exists():assert sha(canon)==x['source_sha256'];canonical+=1
    else:assert key=='CompilerSequenceCompletion',name
for name,x in m['receipts'].items():
    p=ROOT/x['receipt'];r=json.loads(p.read_text());assert sha(p)==x['receipt_sha256'] and r['status']=='passed' and r['exit']==0
    assert sha(S/'project/ShielddSecurity'/(name+'.lean'))==x['source_sha256']
    assert sha(S/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean'))==x['object_sha256']
    assert r['axiom_audits']==x['audits']
a=m['attribution_successor'];ap=ROOT/a['receipt'];r=json.loads(ap.read_text());src=ROOT/a['source'];old=S/'project/ShielddSecurity'/src.name
assert sha(ap)==a['receipt_sha256'] and sha(src)==a['source_sha256'] and r['status']=='passed' and r['exit']==0
assert old.read_bytes().split(b'\n',1)[1]==src.read_bytes().split(b'\n',1)[1]
assert r['object_sha256']==a['object_sha256']==m['receipts']['TransferPoseidonWidth3Prefix10AbsorbProof01']['object_sha256']
log=ap.with_suffix('.log');assert sha(log)==r['log_sha256'];text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert sorted(n for n,_ in axioms)==sorted(r['expected_axiom_names'])
for n,v in axioms:
    assert {x.strip() for x in v.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
    hits=re.findall(r'^@?'+re.escape(n)+r'\s*:[\s\S]*?(?=^\''+re.escape(n)+r'\')',text,re.M)
    assert len(hits)==1 and hashlib.sha256(hits[0].strip().encode()).hexdigest()==r['full_signature_sha256'][n]
assert len(axioms)==10 and r['lean_heap_limit_MiB']==2048 and r['timeout_seconds']==240 and r['process_group_rss_limit_bytes']==4*1024**3
assert r['seconds']<=240 and r['peak_group_rss_bytes']<=4*1024**3 and r['minimum_memory_free_percent']>=15 and r['minimum_disk_free_bytes']>=2*1024**3
replay=json.loads((H/'byte-replay01/outputs/mac-poseidon-width3-call10/replay-result01.json').read_text());assert len(replay['sources'])==19
assert sum(x['attribution_only_successor'] for x in replay['sources'])==1
result={'schema':'parent-whole-call10-sealed-identities-review-v1','manifest_sha256':sha(mp),'files_rehashed':len(m['files']),'main_fresh_modules':len(m['receipts']),'main_exact_declaration_audits':sum(x['audits'] for x in m['receipts'].values()),'inherited_sources_objects_receipts':len(m['inherited_imports']),'canonical_inherited_sources_checked':canonical,'attribution_successor':{'fresh_source_audits':10,'mathematical_new_credit':0,'comment_only_identical_object':True},'portable_generated_sources':19,'exact_accepted_generated_sources':18,'attribution_only_generated_successor':1,'kernel_runs':0,'full_transfer':'OPEN'}
(H/'seal-audit01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
