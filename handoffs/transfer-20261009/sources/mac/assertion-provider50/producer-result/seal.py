from pathlib import Path
import json,hashlib,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');E=W/'mac-assertion-provider50-execution10';S=W/'mac-assertion-provider50-kernel-result01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(v):
 require(pin(Path(v['path']))==v,'exact identity '+v['path'])
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
c=json.loads((E/'config01.json').read_bytes());history=json.loads(Path(c['carried_failure']['path']).read_bytes());rps=history['receipts']+[pin(p)for p in sorted((E/'runtime/receipts').glob('*.json'))];allrs=[json.loads(Path(p['path']).read_bytes())for p in rps]
require(len(allrs)==400 and sum(r['status']=='failed'for r in allrs)==13,'complete retained provider phase')
selected={}
for rp,r in zip(rps,allrs):
 if r['status']!='passed':continue
 n=r['module']
 if n.startswith('CapturedAssertions50B')or n.startswith('CapturedAssertions54G')or n in ['CapturedFullAssertions54','CapturedAssertionLinks57','CapturedAssertionControls56','AssertionCoefficients50']:selected[n]=(rp,r)
require(len(selected)==100,'ninety leaves, six groups, root, three support/control/link modules')
S.mkdir();(S/'seal.py').write_bytes(Path(__file__).read_bytes());mods={};audits=[];refs={}
for n,(rp,r)in selected.items():
 for v in [rp,r['source'],r['stdout'],r['stderr'],*r['objects'].values()]:check(v)
 for a in r['audits']:
  require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'full type hash')
  require(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  audits.append(dict(module=n,receipt=rp,**a))
 mods[n]=dict(source=r['source'],objects=r['objects'],receipt=rp,stdout=r['stdout'],stderr=r['stderr'],audits=len(r['audits']),lean_seconds=r['lean_seconds'],rss=r['peak_group_rss'],scope='Exact named original fresh execution; retained qualified object, not a replay')
refs['qualified_mods']=mods
write('qualified-modules01.json',mods);write('full-audits01.json',audits)
write('failed-attempts01.json',[dict(receipt=rp,source=r['source'],stdout=r['stdout'],stderr=r['stderr'],status='ZERO kernel credit')for rp,r in zip(rps,allrs)if r['status']=='failed'])
write('scope01.json',dict(modules=len(mods),complete_types=len(audits),leaves=90,positions=22816,assertions=22813,verifier_links=3,source_mixture='27 accepted source04 and63 literal-coefficient source06 leaves; same exact checker',controls='Four finite syntax/pair-size refusals, two positives; omission is list-size refusal, not full coverage semantic inequality.',formal_scope='Complete indexed original outlined assertion-row provider; all positions exist; bidirectional field-polynomial equivalence; final-row public/committed/copy bindings derived without copy truth premise.',open=['legal-input assertion truth','original graph evaluation/caller meaning','native/Rust refinement','full200770-row composition until arithmetic provider closes','full Transfer'],all_retained_attempts=400,all_retained_lean_seconds=sum(r['lean_seconds']for r in allrs),all_failed=13,source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',runtime='844389ee069e1fb2e576708842d0b389b4d9a44a'))
for root in ['mac-assertion-provider50-source01','mac-assertion-provider50-source04','mac-assertion-provider50-source06','mac-assertion-root54-source01','mac-assertion-controls56-source01','mac-assertion-links57-source01','mac-assertion-links57-source02','mac-assertion-provider50-portable-source01']:
 for p in (W/root).rglob('*'):
  if p.is_file():refs[str(p)]=pin(p)
refs['official_manifest']=c['official'];refs['original_inherited_closure']=c['closure'];refs['carried_history']=c['carried_failure'];refs['final_ledger']=pin(E/'runtime/ledger.jsonl')
write('references01.json',refs)
entries={str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()}
write('producer-manifest01.json',entries);write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),scope=pin(S/'scope01.json'),raw_logs_and_objects='Local immutable references only; omit from publication',portable_recipe=pin(W/'mac-assertion-provider50-portable-source01/producer-manifest01.json')))
for v in entries.values():check(v)
write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),all_producer_entries_unchanged=True))
print(json.dumps(dict(producer=pin(S/'producer-manifest01.json'),modules=len(mods),audits=len(audits))))
