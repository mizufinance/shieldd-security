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
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.CapturedNextHighShared136.'+n for n in ['completed', 'claimed_seed', 'legal_registry_global1332']]
t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits);require(len(t.encode())<=262144,'finite source');p=r/'CapturedNextHighShared136.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedNextHighShared136',source=pin(p),audits=audits)],generator=pin(Path(__file__)),template=pin(S/'template.lean'),scope='Same-final-assignment all arithmetic and actual130 high-limb assertions. Both limb meanings derived from original255 seed bits and independent bounded Nat division; no desired truth/initial satisfaction premise. Prior938 truth preservation/legal original roles remain separate.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
