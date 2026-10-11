from pathlib import Path
import hashlib,json,re,sys
S=Path(__file__).resolve().parent
G=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff/circuits/ShielddSecurity')
def require(ok,message):
 if not ok:raise ValueError(message)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(name,value):
 with(S/name).open('x')as f:f.write(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable source emission')
pins=json.loads((S/'input-pins01.json').read_bytes());outputs=[]
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True)
for name in ['TransferCore','TransferSem']:
 p=G/(name+'.lean');require(pin(p)==pins[name],'exact canonical independent semantics')
 t=p.read_text();t=re.sub(r'(?m)^set_option maxHeartbeats 200000$', 'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192',t)
 t=re.sub(r'(?m)^set_option pp.all true in\n#check [^\n]*\n?', '', t)
 t=re.sub(r'(?m)^#(?:check|print axioms) [^\n]*\n?', '', t)
 if name=='TransferSem':t=t.replace('set_option maxRecDepth 8192','set_option maxRecDepth 8192\nset_option linter.dupNamespace false',1)
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem|structure|inductive) ([\w.]+)',t,re.M)
 require(len(names)==len(set(names)),'complete distinct independent declarations')
 qualified=['ShielddSecurity.'+name+'.'+n for n in names]
 t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n' for n in qualified)
 with(r/(name+'.lean')).open('x')as f:f.write(t)
 outputs.append(dict(name=name,source=pin(r/(name+'.lean')),audits=qualified,original=pins[name],fresh_credit=0))
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==6,'complete six epoch semantic declarations')
qualified=['ShielddSecurity.CapturedRegistryEpoch66.'+n for n in names]
t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in qualified)
with(r/'CapturedRegistryEpoch66.lean').open('x')as f:f.write(t)
outputs.append(dict(name='CapturedRegistryEpoch66',source=pin(r/'CapturedRegistryEpoch66.lean'),audits=qualified,fresh_credit=0))
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),inputs=pins,outputs=outputs,scope='SOURCE UNRUN. Independent RegistrySem supplies epoch legality, then actual global arithmetic completion derives69 epoch assertion rows. No full legal-Transfer construction or native interpretation asserted.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=outputs)))
