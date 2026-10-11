from pathlib import Path
import json,hashlib,re,sys
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem|instance) (\w+)',t,re.M);require(len(names)==len(set(names))==20,'complete 20 declarations')
matches=list(re.finditer(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M));out=t[:matches[0].start()]
for i,m in enumerate(matches):
 out+=t[m.start():matches[i+1].start()if i+1<len(matches)else len(t)]+'\n'+f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRegistryValueRange97.{m[1]}\n#print axioms ShielddSecurity.CapturedRegistryValueRange97.{m[1]}\n'
t=out
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRegistryValueRange97.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),primary_arithmetic='Exact qualified Group78 and polynomial79; no raw source/model claim',source=pin(p),audits=['ShielddSecurity.CapturedRegistryValueRange97.'+n for n in names],scope='SOURCE UNRUN: finite source column frame facts from RegistrySem, source-role meanings, independent preimage-eight binding/curve and field certificates. No desired row/assertion/hash truth premises. Remaining22653assertions/native/full Transfer OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
