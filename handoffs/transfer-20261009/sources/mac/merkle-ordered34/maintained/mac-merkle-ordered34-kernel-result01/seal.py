from pathlib import Path
import json,hashlib,re
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent;Q=R/'work/mac-merkle-ordered34-source04'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
rp=Q/'runtime/receipts/173-MerkleOrdered34.json';d=json.loads(rp.read_bytes());require(d['status']=='passed' and d['exit']==0 and type(d['exit'])is int,'accepted')
source=Path(d['source']['path']);template=(Q/'template.lean').read_text();names=re.findall(r'^\s*(?:def|theorem) (\w+)',template,re.M);derived=template+'\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.MerkleOrdered34.{n}\n#print axioms ShielddSecurity.MerkleOrdered34.{n}\n'for n in names);require(source.read_bytes()==derived.encode(),'exact in-memory replay')
for a in d['audits']:
 require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'full signature hash');require(set(a['axioms'])<={'propext','Quot.sound','Classical.choice'},'axioms')
require(len(names)==len(d['audits'])==9,'complete declaration census')
write('qualified-modules01.json',dict(module='MerkleOrdered34',source=d['source'],objects=d['objects'],receipt=pin(rp),stdout=d['stdout'],stderr=d['stderr'],cleanup=d['cleanup'],lean_seconds=d['lean_seconds'],peak_group_rss=d['peak_group_rss']))
write('full-audits01.json',d['audits']);write('maintained-references01.json',[pin(Q/x)for x in ['generate.py','template.lean','generation01.json','prepare_continuation.py','config01.json','maintained/guard.py','maintained-inventory01.json']])
f=[]
for i,n in [(170,'01'),(171,'02'),(172,'03')]:
 p=R/f'work/mac-merkle-ordered34-source{n}/runtime/receipts/{i}-MerkleOrdered34.json';r=json.loads(p.read_bytes());require(r['status']!='passed','failure retained');f.append(dict(receipt=pin(p),source=r['source'],stdout=r['stdout'],stderr=r['stderr'],error=r['error'],lean_seconds=r['lean_seconds'],cleanup=r['cleanup'],proof_credit=0))
write('execution-census01.json',dict(accepted_modules=1,complete_reports=9,all_historical_attempts=d['all_attempts'],all_historical_seconds=d['all_lean_seconds'],failed_predecessors=f))
write('scope01.json',dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',frozen_source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',claims=['All32 actual bit rows imply a Boolean encoding used by16 ordered quaternary child-insertion levels','Same final assignment root from independent original-input Registry meaning; output literalLC and actualanchor soundness','Existing constructor seeds32 hints from n<2^32 and preserves declared fixed/outside columns'],residual=['Field F and CharP F pinnedp','Soundness one plus selected prior/first/rest/bit/anchor rows, not desiredhashtruth','Constructor originalposition=castn, one and copy linkage; anchor requires independently stated legal root','Full captured rowAt/globalpartition, native Rust/TransferSem, total wholeTransfer construction OPEN'],unseeded_hints_preserved=False,booleans_not_yet_bound_to_a_single_recovered_position_integer=True,qualified_custom_imports=d['inherited_closure'],official_manifest=d['official_manifest'],portable_full_import_generation='OPEN'))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),parent_path_endpoint=pin(R/'work/mac-merkle-path33-kernel-result01/producer-manifest01.json')));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(pin(S/'producer-manifest01.json')))
