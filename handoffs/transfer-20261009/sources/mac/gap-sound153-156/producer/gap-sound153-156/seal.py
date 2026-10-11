from pathlib import Path
import hashlib,json,re,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');E=W/'mac-full-arithmetic45-execution178';S=W/'mac-gap-sound153-156-kernel-result01'
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
specs=[]
for dirname in ['mac-next-high-sound153-source01','mac-next-low-sound154-source01','mac-zero-flag-sound155-source02','mac-registry-gap-sound156-source02']:
 g=json.loads((W/dirname/'generation01.json').read_bytes());specs+=g['outputs']
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
require(len(qualified)==4 and len(fulltypes)==22,'exact full relation/fixed/epoch/zero inventory')
require(not S.exists(),'new immutable seal');S.mkdir();(S/'seal.py').write_bytes(Path(__file__).read_bytes())
put('qualified-modules01.json',qualified);put('full-audits01.json',fulltypes)
put('attempt-history01.json',dict(receipts=identities,passed=sum(r['status']=='passed'for _,r in receipts),failed=[dict(receipt=i,status=r['status'],module=r['module'],error=r['error'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],fresh_proof_credit=0)for i,r in receipts if r['status']!='passed'],all_attempts=len(receipts),all_lean_seconds=sum(r['lean_seconds']for _,r in receipts),full_failure_credit=0))
put('scope01.json',dict(modules=4,reports=22,meaning='Arbitrary satisfying full200770 relation derives both zero flags and next high/low borrow hints from actual rows. With rho0=1, unregulated role rho10=0, independently canonical value/asset/next and exact six bit-limb meanings, actual gap assertion derives value<asset<next. No desired ordering/RegistrySem/initial-row/hash-truth premise. Canonical/bit meaning recovery remains separate OPEN; shared constructor1467 unchanged. Failed sources wholeZERO/native/fullTransferOPEN.'))
put('archived-history-inputs01.json',dict(map=pin(W/'mac-history-metadata-preservation126-12/archive-map01.json'),guard=pin(E/'maintained/guard.py'),instruction='Original config path/hash/bytes remain authoritative. Resolve absent original through exact immutable map entry and pinned bounded-LZMA archive, preserving original bytes. Do not restore large histories or label archives fresh execution.'))
put('maintained-references01.json',[pin(p)for dirname in ['mac-next-high-sound153-source01','mac-next-low-sound154-source01','mac-zero-flag-sound155-source02','mac-registry-gap-sound156-source02']for p in (W/dirname).rglob('*')if p.is_file()]+[pin(p)for p in [E/'maintained/guard.py',E/'maintained/prepare.py',E/'dispatcher/serial.py',E/'config01.json',E/'maintained-inventory01.json',E/'plan01.json']])
replay=[]
for dirname in ['mac-next-high-sound153-source01','mac-next-low-sound154-source01','mac-zero-flag-sound155-source02','mac-registry-gap-sound156-source02']:
 root=W/dirname;g=json.loads((root/'generation01.json').read_bytes());out=g['outputs'][0];data=(root/'template.lean').read_text()+'\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in out['audits']);require(data.encode()==verified(out['source']),'in-memory maintained byte regeneration');replay.append(dict(source=out['source'],template=pin(root/'template.lean'),generator=pin(root/'generate.py'),byte_identical=True,kernel_replay=False))
put('byte-replay01.json',replay)
(S/'ledger-observation01.jsonl').write_bytes((E/'runtime/ledger.jsonl').read_bytes())
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),ledger_observation=pin(S/'ledger-observation01.jsonl'),historical_provenance=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),guard=pin(S/'postseal-guard01.json'),modules=4,audits=22)))
