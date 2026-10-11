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
data=(S/'selected-data01.json').read_bytes();require(hashlib.sha256(data).hexdigest()=='1f9ae3c40503b7876b16f4df16802f33b0fc9f89f902f84ad15894b8b9e0ee4e','frozen DATA before rendering');v=json.loads(data)
def lc(a):return '['+','.join('('+str(i)+','+str(x)+')'for i,x in a)+']'
def row(r):return '⟨'+lc(r['a'])+','+lc(r['b'])+'⟩'
t=(S/'template.lean').read_text().replace('@AR@','['+','.join(row(r)for r in v['rows'][:2])+']').replace('@AS@','['+row(v['rows'][2])+']');names=re.findall(r'^(?:noncomputable )?(?:def|theorem|instance) (\w+)',t,re.M);require(len(names)==len(set(names))==14,'complete fourteen declarations')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRegulatedAsset95.{n}\n#print axioms ShielddSecurity.CapturedRegulatedAsset95.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRegulatedAsset95.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),primary_arithmetic='Exact qualified Group78 and polynomial79; no raw source/model claim',source=pin(p),audits=['ShielddSecurity.CapturedRegulatedAsset95.'+n for n in names],scope='SOURCE UNRUN: finite source column frame facts from RegistrySem, source-role meanings, independent preimage-eight binding/curve and field certificates. No desired row/assertion/hash truth premises. Remaining22653assertions/native/full Transfer OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
