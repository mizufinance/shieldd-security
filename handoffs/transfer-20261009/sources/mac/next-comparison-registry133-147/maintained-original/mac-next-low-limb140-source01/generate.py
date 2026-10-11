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
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.CapturedNextLowLimb140.'+n for n in ['columns','leftColumns','rightColumns','expected','actual','productionCheck','production_checked','block','hint_exact','full_position']]
t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits);require(len(t.encode())<=262144,'finite source');p=r/'CapturedNextLowLimb140.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedNextLowLimb140',source=pin(p),audits=audits)],selected_data={'path': '/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-next-low-limb140-data01/selected-data01.json', 'bytes': 86017, 'sha256': '2cc2e2a9832e862dd57f14f3f66483c2d494abad9d2042f04fb151f9fd87f9f6'},generator=pin(Path(__file__)),template=pin(S/'template.lean'),scope='Second low128 limb: actual131 assertions179290..179420; finite exact row/recipe checker and positional association, no assertion-truth premise.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
