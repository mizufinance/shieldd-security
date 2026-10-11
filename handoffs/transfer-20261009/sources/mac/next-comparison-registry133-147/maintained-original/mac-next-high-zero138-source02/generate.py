from pathlib import Path
import sys,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
data=S.parent/'mac-next-high-zero137-data01/selected-data01.json';v=pin(data);require(v['bytes']==144573 and v['sha256']=='79b1d51bccf7e12e2669e21012db1792c88ec667986e7a14072239ed34d48fd6','exact independent actual-row data');d=json.loads(data.read_bytes())
def linear(ts):return '['+','.join('('+str(x)+','+str(y)+')'for x,y in ts)+']'
def rows(rs):return '['+','.join('⟨'+linear(x['outlined_a'])+','+linear(x['outlined_b'])+'⟩'for x in rs)+']'
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.CapturedNextHighZero138.'+n for n in ['delta', 'arithmeticRows', 'actualRows', 'arithmeticCheck', 'arithmetic_checked', 'assertionCheck', 'assertion_checked', 'inverseCheck', 'inverse_checked', 'zeroCheck', 'zero_checked', 'expected', 'productionCheck', 'production_checked', 'block', 'hint_exact', 'arithmetic_position', 'assertion_position', 'products', 'truth', 'complete']]
require(len(t.encode())<=262144,'finite source');p=r/'CapturedNextHighZero138.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedNextHighZero138',source=pin(p),audits=audits)],generator=pin(Path(__file__)),template=pin(S/'template.lean'),data=v,scope='Actual second high-limb isZero: two captured product pairs11040..11043, three assertion positions179287..179289. Independent finite syntax checks/standard arithmetic soundness; explicit field flag/inverse numeric meanings remain. No desired truth/semantic/native claim.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
