from pathlib import Path
import json,hashlib,re,sys
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=Path(__file__).resolve().parent

def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,x):
 with(S/n).open('x')as f:json.dump(x,f,sort_keys=True,separators=(',',':'));f.write('\n')
def declarations(text):
 stack=[];out=[]
 for line in text.splitlines():
  m=re.match(r'^namespace ([\w.]+)$',line)
  if m:stack.append(m[1]);continue
  if re.match(r'^end (?:[\w.]+)$',line):
   require(stack,'namespace closure');stack.pop();continue
  m=re.match(r'^\s*(?:def|theorem|abbrev|structure) (\w+)',line)
  if m:out.append('.'.join(stack+[m[1]]))
 return out
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
stages=['mac-merkle-family32-binding-leaves01','mac-segment-chain33-source02','mac-merkle-family32-tables04','mac-merkle-family32-whole06','mac-merkle-path33-source03','mac-merkle-path33-frame01','mac-merkle-path33-meaning02','mac-merkle-path33-meaning03']
mods={};audits=[];refs=[];ledgers=[]
for stage in stages:
 P=R/stage;ledgers.append(pin(P/'runtime/ledger.jsonl'))
 for rp in sorted((P/'runtime/receipts').glob('*.json')):
  d=json.loads(rp.read_bytes())
  if d['status']!='passed':continue
  require(d['cleanup']['clean']and type(d['exit'])is int and d['exit']==0,'pass')
  require(d['module']not in mods,'one accepted association')
  source=Path(d['source']['path']);require(pin(source)==d['source'],'source');text=source.read_text();expected=declarations(text);named=re.findall(r'^#check @([\w.]+)',text,re.M)
  require(set(expected)==set(named)==set(a['name']for a in d['audits'])and len(expected)==len(named)==len(d['audits']),'complete public declaration audit census')
  for a in d['audits']:
   require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'type hash');require(set(a['axioms'])<=set(['propext','Quot.sound','Classical.choice']),'standard axioms');audits.append(dict(a,receipt=pin(rp)))
  for record in list(d['objects'].values())+[d['stdout'],d['stderr']]:require(pin(Path(record['path']))==record,'object/log identity')
  mods[d['module']]={k:d[k]for k in ['source','objects','stdout','stderr','lean_seconds','peak_group_rss','cleanup','all_attempts']};mods[d['module']].update(receipt=pin(rp),audits=len(d['audits']))
 for name in ['generate.py','generation01.json','template.lean','extract.py','selected-data01.json','prepare_continuation.py','maintained/guard.py','config01.json','maintained-inventory01.json','producer-manifest01.json','envelope01.json','postseal-guard01.json']:
  p=P/name
  if p.is_file():refs.append(pin(p))
require(len(mods)==22 and len(audits)==224,'22accepted224reports')
failstages=['mac-merkle-family32-tables02','mac-merkle-family32-tables03','mac-merkle-family32-whole03','mac-merkle-family32-whole04','mac-merkle-family32-whole05','mac-merkle-path33-source01','mac-merkle-path33-source02','mac-merkle-path33-meaning02'];failed=[]
for stage in failstages:
 for rp in (R/stage/'runtime/receipts').glob('*.json'):
  d=json.loads(rp.read_bytes())
  if d['status']=='failed':failed.append(dict(receipt=pin(rp),source=d['source'],stdout=d['stdout'],stderr=d['stderr'],zero_credit=True,reason=d['error'],seconds=d['lean_seconds'],cleanup=d['cleanup']))
require(len(failed)==8,'eight retained failed predecessors')
P=R/'mac-merkle-path33-meaning03';last=json.loads(next((P/'runtime/receipts').glob('*.json')).read_bytes());cfg=json.loads((P/'config01.json').read_bytes())
put('qualified-modules01.json',mods);put('full-audits01.json',audits)
put('execution-census01.json',dict(accepted=22,audits=224,accepted_lean_seconds=sum(d['lean_seconds']for d in mods.values()),peak_group_rss=max(d['peak_group_rss']for d in mods.values()),failed_predecessors=failed,ledgers=ledgers,all_historical_attempts=last['all_attempts'],all_historical_lean_seconds=last['all_lean_seconds'],limits=dict(threads=1,jobs=1,heap_mib=2048,module_seconds=240,group_rss_bytes=4294967296,min_free_memory_percent=15,min_free_disk_bytes=2147483648,max_heartbeats=900000,max_recursion=8192)))
put('maintained-references01.json',refs+[pin(Path(__file__))])
put('scope01.json',dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',qualified='All15 actual remaining port/seam/output/predecessor LC certificates; symbolic Segment chain constructs all component rows from arbitrary copy-linked base and preserves earlier actual supports. Same-final-rho field-polynomial16-level root using independently defined original-input first-root meaning. Literal anchor row178117/assertion163 checked against result raw115245. Soundness derives original column4 equals root. Completeness constructs prefix/hash/Boolean/path rows, then anchor under independent legal_anchor semantic equality.',premises=['Field F; CharP F exact BLS12-381 scalar modulus p','soundness:rho0=1 plus actual local/component row satisfaction; no desired hash conclusion premise','constructor:base0=1,basecopy=base0,n<2^32,base135=castn;anchor completeness additionally base4=independent semantic root of seeded original inputs'],preservation='Chain preserves outside[25884,32244); combined prefix preserves outside[22738,32244) after explicitly seeding only32bit-hintcolumns184..215. Unseeded32hints not preserved. Verifier public/committed/zero/copy and other original columns preserved.',representation='Component collection includes repeated tautological copy rows/steps. Exact arithmetic body/phase port DATA associations and qualified translated tail templates are retained; all-target literal tail/global rowAt partition remains OPEN. Do not interpret aggregate list length as distinct capture positions.',open=['remaining-level ordered Boolean-child interpretation join','formal full indexed original rowAt inclusion/partition and all-target literal tail equality','remaining captured arithmetic/deferred assertions/full TransferSem and native/callsite correspondence','full legal-input Transfer constructor and full200770-row relation'],logs='Raw logs/objects retained local, not publication. Historical failures are zero proof credit. Generator recipes reference exact original local inputs; portable full generation/dependency integration remains OPEN.'))
put('inherited-closure-reference01.json',dict(custom=cfg['closure'],qualified_batch_imports=cfg['qualified_batch_imports'],official=cfg['official'],packages=cfg['packages'],toolchain=cfg['toolchain']) if all(k in cfg for k in ['packages','toolchain']) else dict(config=pin(P/'config01.json'),official=cfg['official'],custom=cfg['closure'],qualified_batch_imports=cfg['qualified_batch_imports']))
put('producer-manifest01.json',{p.name:pin(p)for p in S.iterdir()if p.is_file()})
put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),final_stage_producer=pin(P/'producer-manifest01.json'),failed_history=pin(P/'protected-history01.json')))
require(all(pin(Path(p['path']))==p for p in json.loads((S/'producer-manifest01.json').read_bytes()).values()),'post seal identities')
put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),all_entries_rehashed=True))
print(json.dumps(dict(producer=pin(S/'producer-manifest01.json'),accepted=22,audits=224,all_attempts=last['all_attempts'],all_seconds=last['all_lean_seconds'])))
