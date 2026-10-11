from pathlib import Path
import hashlib,json,re,sys,lzma
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');E=W/'mac-full-arithmetic45-execution202';S=W/'mac-merkle-global-body181-kernel-result01'
def require(ok,message):
 if not ok:raise ValueError(message)
def pin(p):
 p=Path(p)
 if not p.exists():return archived(p)[0]['original']
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def archived(path):
 record=json.loads((W/'mac-history-metadata-preservation126-18/archive-map01.json').read_bytes())['records'][str(path)]
 require(pin(record['archive']['path'])==record['archive'],'exact stored archive')
 decoder=lzma.LZMADecompressor();raw=decoder.decompress(Path(record['archive']['path']).read_bytes(),max_length=record['original']['bytes']+1)
 require(decoder.eof and not decoder.unused_data and len(raw)==record['original']['bytes'] and hashlib.sha256(raw).hexdigest()==record['original']['sha256'],'bounded exact original bytes')
 return record,raw
def verified(identity):
 require(pin(identity['path'])==identity,'exact file identity');return Path(identity['path']).read_bytes()
def put(n,value):
 with(S/n).open('x')as f:f.write(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
c=json.loads(verified(pin(E/'config01.json')));h=json.loads(verified(c['carried_failure']));identities=h['receipts']+[pin(p)for p in sorted((E/'runtime/receipts').glob('*.json'))[:1]]
receipts=[(identity,json.loads(verified(identity)))for identity in identities]
specs=[]
for dirname in ['mac-merkle-global-body181-source02']:
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
require(len(qualified)==1 and len(fulltypes)==12,'exact full relation/fixed/epoch/zero inventory')
require(not S.exists(),'new immutable seal');S.mkdir();(S/'seal.py').write_bytes(Path(__file__).read_bytes())
put('qualified-modules01.json',qualified);put('full-audits01.json',fulltypes)
put('attempt-history01.json',dict(receipts=identities,passed=sum(r['status']=='passed'for _,r in receipts),failed=[dict(receipt=i,status=r['status'],module=r['module'],error=r['error'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],fresh_proof_credit=0)for i,r in receipts if r['status']!='passed'],all_attempts=len(receipts),all_lean_seconds=sum(r['lean_seconds']for _,r in receipts),full_failure_credit=0))
put('scope01.json',dict(modules=1,reports=12,meaning='Transparent field-independent row projection of qualified MerkleFamily32Whole; exact generic concatenation seam and arithmetic/copy satisfaction composition. Actual arithmetic subset still requires full indexed captured-row certificates; copyCheck true still requires finite instance qualification. No final full-path/global-hash/legal/native conclusion. One fresh helper, all inherited modules zero fresh replay. Failed ambiguous-namespace predecessor is retained whole-zero. Snapshot through1024; later live records are excluded from this balanced immutable first-result prefix.'))
put('archived-history-inputs01.json',dict(map=pin(W/'mac-history-metadata-preservation126-18/archive-map01.json'),guard=pin(E/'maintained/guard.py'),instruction='Original config path/hash/bytes remain authoritative. Resolve absent original through exact immutable map entry and pinned bounded-LZMA archive, preserving original bytes. Do not restore large histories or label archives fresh execution.'))
put('maintained-references01.json',[pin(p)for dirname in ['mac-merkle-global-body181-source02']for p in (W/dirname).rglob('*')if p.is_file()]+[pin(p)for p in [E/'maintained/guard.py',E/'maintained/prepare.py',E/'dispatcher/serial.py',E/'config01.json',E/'maintained-inventory01.json',E/'plan01.json']])
replay=[]
for spec in specs:
 root=Path(spec['source']['path']).parent.parent.parent
 template=root/(spec['name']+'.template.lean')
 if not template.exists():template=root/'template.lean'
 data=template.read_text()+'\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in spec['audits'])
 require(data.encode()==verified(spec['source']),'in-memory maintained byte regeneration')
 replay.append(dict(source=spec['source'],template=pin(template),generator=pin(root/'generate.py'),byte_identical=True,kernel_replay=False))
put('byte-replay01.json',replay)
lines=(E/'runtime/ledger.jsonl').read_bytes().splitlines(keepends=True)
require(len(lines)>=2 and all(line.endswith(b'\n')for line in lines[:2]),'complete one-result immutable ledger prefix')
require(all(json.loads(lines[i])['kind']==('intent' if i%2==0 else 'result')for i in range(2)),'balanced one-result ledger prefix')
(S/'ledger-observation01.jsonl').write_bytes(b''.join(lines[:2]))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),ledger_observation=pin(S/'ledger-observation01.jsonl'),historical_provenance=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),guard=pin(S/'postseal-guard01.json'),modules=1,audits=12)))
