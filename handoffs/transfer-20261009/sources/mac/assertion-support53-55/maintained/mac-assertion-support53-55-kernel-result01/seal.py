from pathlib import Path
import json,hashlib,re
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
items=[('mac-verifier-links53-source03','mac-assertion-provider50-execution04','CompilerVerifierLinks53',263),('mac-assertion-pairs55-source02','mac-assertion-provider50-execution05','CompilerAssertionPairs55',265)]
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
modules=[];audits=[];refs=[];replays=[]
for stage,execution,name,index in items:
 q=R/'work'/stage;e=R/'work'/execution;rp=e/f'runtime/receipts/{index}-{name}.json';d=json.loads(rp.read_bytes())
 require(d['status']=='passed' and type(d['exit'])is int and d['exit']==0 and d['cleanup']['clean'],'qualified complete narrow execution')
 src=Path(d['source']['path']);public=re.findall(r'^(?:noncomputable )?(?:def|theorem|inductive|abbrev|structure) (\w+)',(q/'template.lean').read_text(),re.M);planned=re.findall(r'^#check @([\w.]+)',src.read_text(),re.M)
 require(len(public)==len(planned)==len(d['audits']) and set(planned)=={a['name'] for a in d['audits']},'every public declaration audited')
 for a in d['audits']:
  require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'exact complete signature hash');require(set(a['axioms'])<={'propext','Quot.sound','Classical.choice'},'standard axioms only')
 expected=(q/'template.lean').read_bytes()+b'\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'for n in public).encode()
 require(expected==src.read_bytes(),'exact original template+maintained audit renderer in memory')
 require(pin(src)==d['source'] and all(pin(Path(p))==v for p,v in d['objects'].items()),'source and all object companions unchanged')
 modules.append(dict(module=name,receipt=pin(rp),source=d['source'],objects=d['objects'],stdout=d['stdout'],stderr=d['stderr'],cleanup=d['cleanup'],lean_seconds=d['lean_seconds'],peak_group_rss=d['peak_group_rss'],custom_imports=d['inherited_closure'],official_imports=d['official_manifest']))
 audits+=d['audits'];refs += [pin(q/x)for x in ['generate.py','template.lean','generation01.json']]+[pin(e/x)for x in ['maintained/guard.py','maintained/prepare.py','maintained-inventory01.json','config01.json','plan01.json','producer-manifest01.json','envelope01.json','postseal-guard01.json']]
 replays.append(dict(generator=pin(q/'generate.py'),template=pin(q/'template.lean'),source=d['source'],bytes_exact=True,scope='Exact maintained identity renderer compared in memory; no physical source copy or Lean replay'))
require(len(audits)==17,'12 link and5 pair reports')
failures=[]
for e,i,n in [('mac-assertion-provider50-execution02',261,'CompilerVerifierLinks53'),('mac-assertion-provider50-execution03',262,'CompilerVerifierLinks53'),('mac-assertion-provider50-execution04',264,'CompilerAssertionPairs55')]:
 p=R/'work'/e/f'runtime/receipts/{i}-{n}.json';d=json.loads(p.read_bytes());require(d['status']=='failed' and d['cleanup']['clean'],'failed predecessors retained cleanly');failures.append(dict(receipt=pin(p),source=d['source'],stdout=d['stdout'],stderr=d['stderr'],credit=0))
write('qualified-modules01.json',modules);write('full-audits01.json',audits);write('maintained-references01.json',refs);write('in-memory-replay01.json',replays);write('failures01.json',failures)
write('scope01.json',dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',accepted_modules=2,complete_reports=17,premises=['Field and CharP for link evaluation','Finite same-checkRow Boolean certificates for expression equivalence','Symbolic list-length equality for pair concatenation'],scope='Generic verifier link equivalence without copy linkage premise; seed constructor preserves original columns. Generic pair checker, indexed coverage, same Boolean append and block bridge. No actual captured link-position or actual assertion leaf instantiated here.',open=['Exact actual last3 provider row identities','Actual assertion leaf checks and full provider','Independent legal-input assertion truth/source evaluator/native/full Transfer']))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),accepted_assertion51=pin(R/'work/mac-assertion-block51-kernel-result01/producer-manifest01.json')));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(pin(S/'producer-manifest01.json')))
