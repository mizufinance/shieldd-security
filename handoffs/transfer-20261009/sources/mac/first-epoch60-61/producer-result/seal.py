from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent;W=S.parent

def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
def validate(v):require(pin(v['path'])==v,'exact '+v['path'])
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists(),'immutable sealing')
items=[('mac-first-epoch-range60-source02','CapturedEpochRange60','mac-full-arithmetic45-execution14',530,'generate02.py',18),('mac-first-epoch-nonzero61-source04','CapturedEpochNonzero61','mac-full-arithmetic45-execution16',532,'generate.py',24)]
modules=[];audits=[];refs=[];replays=[];closure=[]
for stage,name,ex,index,gen,count in items:
 q=W/stage;rp=W/ex/'runtime/receipts'/f'{index}-{name}.json';r=json.loads(rp.read_bytes())
 require(r['status']=='passed' and type(r['exit'])is int and r['exit']==0 and r['error'] is None and r['cleanup']['clean'] and not r['cleanup']['errors'],'actual passed cleanup')
 for v in [r['source'],r['stdout'],r['stderr'],*r['objects'].values()]:validate(v)
 generation=json.loads((q/'generation01.json').read_bytes());require(generation['audits']==[a['name']for a in r['audits']] and len(r['audits'])==count,'complete named audits')
 template=(q/'template.lean').read_text();pattern=r'^(?:noncomputable )?(?:def|theorem) (\w+)' if count==18 else r'^(?:noncomputable )?(?:local )?(?:def|theorem|instance) (\w+)'
 names=re.findall(pattern,template,re.M);require(len(names)==len(set(names))==count,'all declarations')
 rendered=template+'\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'for n in names)
 require(rendered.encode()==Path(r['source']['path']).read_bytes(),'in-memory maintained-render bytes')
 for a in r['audits']:
  require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'exact signature hash')
  require(set(a['axioms'])<={'propext','Quot.sound','Classical.choice'},'standard axioms')
 audits+=r['audits'];modules.append(dict(module=name,receipt=pin(rp),source=r['source'],objects=r['objects'],stdout=r['stdout'],stderr=r['stderr'],cleanup=r['cleanup'],lean_seconds=r['lean_seconds'],peak_group_rss=r['peak_group_rss']))
 files=[p for p in q.rglob('*')if p.is_file()];refs.extend(pin(p)for p in files)
 replays.append(dict(generator=pin(q/gen),template=pin(q/'template.lean'),source=r['source'],scope='Independent in-memory reproduction of the maintained exact rendering algorithm; original generator/qualifier not rerun, no second physical source copy or Lean replay'))
 cfg=json.loads((W/ex/'config01.json').read_bytes());closure.append(dict(config=pin(W/ex/'config01.json'),guard=pin(W/ex/'maintained/guard.py'),inventory=pin(W/ex/'maintained-inventory01.json'),inherited=r['inherited_closure'],official=r['official_manifest'],load_context='Actual guarded first-PACKAGE own alias layout with complete custom and official import checks; inherited zero fresh credit'))
failures=[]
for ex,index,name in [('mac-full-arithmetic45-execution13',529,'CapturedEpochRange60'),('mac-full-arithmetic45-execution14',531,'CapturedEpochNonzero61')]:
 p=W/ex/'runtime/receipts'/f'{index}-{name}.json';r=json.loads(p.read_bytes());require(r['status']!='passed','retained failure')
 failures.append(dict(receipt=pin(p),source=r['source'],stdout=r['stdout'],stderr=r['stderr'],error=r['error'],status=r['status'],cleanup=r['cleanup'],formal_credit=0))
source_predecessors=[]
for stage in ['mac-first-epoch-range60-source01','mac-first-epoch-nonzero61-source01','mac-first-epoch-nonzero61-source02','mac-first-epoch-nonzero61-source03','mac-full-arithmetic45-execution15']:
 q=W/stage
 source_predecessors.append(dict(stage=str(q),sealed_producer=pin(q/'producer-manifest01.json')if(q/'producer-manifest01.json').exists()else None,files=[pin(p)for p in q.rglob('*')if p.is_file() and (p.suffix in ['.py','.lean'] or 'refusal' in p.name or 'producer' in p.name)],fresh_kernel_credit=0,scope='Historical SOURCE/API/preparation failures retained; only actual failed529/531 were Lean attempts'))
put('qualified-modules01.json',modules);put('full-audits01.json',audits);put('maintained-references01.json',refs);put('in-memory-replay01.json',replays);put('load-closure01.json',closure);put('failures01.json',dict(kernel=failures,source_predecessors=source_predecessors))
put('scope01.json',dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',fresh_modules=2,complete_reports=42,range=dict(actual_positions=[177979,178044],source_input=31,column=34,owned_hints=[49,113],constructor_premises=['Field/CharP p','independent n<2^64 and base34=cast n','copy linkage'],result='Actual65-row soundness gives a field representation by a bounded64-bit integer; independent hint constructor satisfies those rows.'),nonzero=dict(arithmetic_positions=[256,262],assertion_positions=[178044,178048],raw_products=[426,429,430],owned_hints=[113,114],constructor_premise='base34=0 implies base10=0; primitive-to-assertion theorem additionally uses constructed six-row arithmetic satisfaction',result='Actual arithmetic/assertions imply zero-indicator/inverse equations and regulated nonzero epoch. Fixed source products are checked against exact actual rows. Primitive equations yield actual assertions after arithmetic construction.'),frame='Owned hint columns are changed; do not claim all22735 original input columns preserved by hint seeding.',open=['Canonical natural-number meaning beyond field representation','Total legal-input semantic hint constructor and all remaining assertions','Full200770-row/arithmetic root qualification','Source graph/native/caller refinement and full Transfer'],failures_zero_credit=True))
put('publication-selection01.json',dict(include=[v for v in refs if not v['path'].endswith('.log')]+[pin(p)for p in S.iterdir()if p.is_file()],exclude='Original stdout/stderr raw logs, objects/compiler caches; references/hashes remain local immutable receipts',fresh_credit='2 modules42 complete reports only; source qualification DATA is not kernel credit'))
put('producer-manifest01.json',{p.name:pin(p)for p in S.iterdir()if p.is_file()})
put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),accepted_assertion_provider=pin(W/'mac-assertion-provider50-kernel-result01/producer-manifest01.json')))
manifest=json.loads((S/'producer-manifest01.json').read_bytes())
for v in manifest.values():validate(v)
put('postseal-guard01.json',dict(status='passed',producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),entries=len(manifest),fresh_modules=2,complete_reports=42))
print(json.dumps(dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),guard=pin(S/'postseal-guard01.json'))))
