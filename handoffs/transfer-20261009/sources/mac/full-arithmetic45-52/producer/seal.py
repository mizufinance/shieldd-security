from pathlib import Path
import hashlib,json,re,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');E=W/'mac-full-arithmetic45-execution21';S=W/'mac-full-arithmetic45-kernel-result01'
def require(ok,message):
 if not ok:raise ValueError(message)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def verified(identity):
 require(pin(identity['path'])==identity,'exact file identity');return Path(identity['path']).read_bytes()
def put(n,value):
 with(S/n).open('x')as f:f.write(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
c=json.loads((E/'config01.json').read_bytes());h=json.loads(verified(c['carried_failure']));identities=h['receipts']+[pin(p)for p in sorted((E/'runtime/receipts').glob('*.json'))]
receipts=[(identity,json.loads(verified(identity)))for identity in identities]
leaves=json.loads((W/'mac-full-arithmetic45-source01/generation01.json').read_bytes())['outputs']
roots=json.loads((W/'mac-full-arithmetic-root52-source01/generation01.json').read_bytes())['outputs'][:-1]+json.loads((W/'mac-full-arithmetic-root52-source02/generation01.json').read_bytes())['outputs'][-1:];specs=leaves+roots
require(len(leaves)==599 and len(roots)==11,'full599 plus ten group certificates and root')
qualified=[];audits=[];fulltypes=[]
for spec in specs:
 name=spec['name'];source=spec['source'];verified(source)
 matches=[(i,r)for i,r in receipts if r['status']=='passed' and r['module']==name and r['source']==source]
 require(len(matches)==1,'exact once qualified source '+name)
 identity,r=matches[0];require(r['exit']==0 and type(r['exit'])is int and r['cleanup']['clean'],'typed successful clean execution')
 require([a['name']for a in r['audits']]==spec['audits'],'complete declared audits')
 for a in r['audits']:
  require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'full type hash')
  require(set(a['axioms'])<= {'propext','Quot.sound','Classical.choice'},'standard axioms only')
 text=verified(r['stdout']).decode();stderr=verified(r['stderr']);require(not stderr,'empty successful stderr')
 extracted=[];remaining=text
 for a in r['audits']:
  n=a['name'];pattern=r'^@?'+re.escape(n)+r'\s*:[\s\S]*?^\''+re.escape(n)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
  m=list(re.finditer(pattern,remaining,re.M));require(len(m)==1,'unique exact raw pair '+n);m=m[0]
  full=m.group(0).split("\n'"+n+"'",1)[0].strip();axs=[]if m.group(1)is None else[x.strip()for x in m.group(1).split(',')if x.strip()]
  require(dict(name=n,full_type=full,full_type_sha256=hashlib.sha256(full.encode()).hexdigest(),axioms=axs)==a,'raw report equals retained receipt')
  extracted.append(a);remaining=remaining[:m.start()]+remaining[m.end():]
 require(not remaining.strip(),'no unexplained raw output')
 for p,o in r['objects'].items():require(pin(p)==o,'qualified companion identity')
 qualified.append(dict(name=name,source=source,objects=r['objects'],receipt=identity,stdout=r['stdout'],stderr=r['stderr'],imports=r['inherited_closure'],official=r['official_manifest'],command=r['command'],reports=len(r['audits']),lean_seconds=r['lean_seconds'],peak_group_rss=r['peak_group_rss'],fresh_execution_credit=1,execution_context='original receipt command/revision; no reattribution to later canonical publication'))
 fulltypes+=extracted
require(len(qualified)==610 and len(fulltypes)==6012,'exactfull arithmetic inventory')
require(not S.exists(),'new immutable seal');S.mkdir();(S/'seal.py').write_bytes(Path(__file__).read_bytes())
put('qualified-modules01.json',qualified);put('full-audits01.json',fulltypes)
put('attempt-history01.json',dict(receipts=identities,passed=sum(r['status']=='passed'for _,r in receipts),failed=[dict(receipt=i,status=r['status'],module=r['module'],error=r['error'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],fresh_proof_credit=0)for i,r in receipts if r['status']!='passed'],all_attempts=len(receipts),all_lean_seconds=sum(r['lean_seconds']for _,r in receipts),full_failure_credit=0))
put('scope01.json',dict(endpoint_modules=610,complete_standard_axiom_reports=6012,arithmetic_positions=177954,squares=50478,products=63738,write_interval=[22738,200692],original_input_count=22735,meaning='Exact indexed collected arithmetic provider and unconditional field construction, unique fresh completion, original-input/verifier/copy/outside frame. This is the complete arithmetic partition, NOT assertion truth, legal-Transfer construction, native compiler/source refinement or full Transfer.',premises=['Field F','CharP F p'],retained_pilots='B0000/B0500/B0598 reused exact initial successful command/source/object; no duplicate compile credit.',data_qualification=pin(W/'mac-full-arithmetic45-source01/qualification01.json'),source_generation=pin(W/'mac-full-arithmetic45-source01/generation01.json'),root_generation=[pin(W/'mac-full-arithmetic-root52-source01/generation01.json'),pin(W/'mac-full-arithmetic-root52-source02/generation01.json')],runtime='844389ee069e1fb2e576708842d0b389b4d9a44a'))
put('maintained-references01.json',[pin(p)for p in [W/'mac-full-arithmetic45-source01/extract.py',W/'mac-full-arithmetic45-source01/generate.py',W/'mac-full-arithmetic-root52-source01/generate.py',W/'mac-full-arithmetic-root52-source02/generate.py',E/'maintained/guard.py',E/'maintained/prepare.py',E/'dispatcher/serial.py',E/'config01.json',E/'maintained-inventory01.json',E/'plan01.json']if p.exists()])
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),ledger_observation=pin(E/'runtime/ledger.jsonl'),historical_provenance=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),guard=pin(S/'postseal-guard01.json'),modules=610,audits=6012)))
