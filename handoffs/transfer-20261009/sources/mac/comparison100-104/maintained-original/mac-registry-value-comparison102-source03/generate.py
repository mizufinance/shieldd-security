from pathlib import Path
import sys,json,re,hashlib
S=Path(__file__).resolve().parent;P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
b=(S/'selected-data01.json').read_bytes();require(len(b)==172696 and hashlib.sha256(b).hexdigest()=='5789daa5244dd0fd0fd12d4180e45821ccc7632481b628499fcc9fa86f48b77d','exact input before decode');d=json.loads(b)
def coeff(v,signed=False):
 if v>P//2:
  return str(v-P)if signed else'((p:Int)'+str(v-P)+')'
 return str(v)
def lc(a,signed=False):return '['+','.join('('+str(x)+','+coeff(v,signed)+')'for x,v in a)+']'
def row(r):return '⟨'+lc(r['a'])+','+lc(r['b'])+'⟩'
def entry(e):return '⟨'+','.join([str(e['bitColumn']),str(e['maximumBit']).lower(),lc(e['before'],True),lc(e['after'],True),str(e['pivot']),str(e['auxiliary']),'['+','.join(row(r)for r in e['rows'])+']'])+'⟩'
t=(S/'template.lean').read_text();part=d['entries'];require(len(part)==254,'bounded first component')
t=t.replace('@ENTRIES@','['+','.join(entry(e)for e in part)+']').replace('@INITIAL@',lc(part[0]['before'],True)).replace('@OUTPUT@',lc(part[-1]['after'],True))
require('@'not in t,'all maintained placeholders emitted')
names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==9,'exact public declaration inventory')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedValueComparison102Full.{n}\n#print axioms ShielddSecurity.CapturedValueComparison102Full.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedValueComparison102Full.lean'
require(len(t.encode())<=262144,'finite source ceiling')
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),data=pin(S/'selected-data01.json'),source=pin(p),audits=['ShielddSecurity.CapturedValueComparison102Full.'+n for n in names],scope='Fresh full254 product/508 actual arithmetic row certificate binding. Legal input comparison and two canonical assertions remainOPEN; exact source DATA recipe replay separately recorded. No desired comparison/row/hash truth premises; arithmetic satisfaction is reusable soundness interface.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
