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
n='MerkleGlobalBody181';names=['selectionRows','phase0Rows','phase1Rows','tailRows','bodyRows','arithmeticRows','copyRows','copyCheck','rows_exact','body_sound','copy_sound','sound']
a=['ShielddSecurity.'+n+'.'+x for x in names];t=(S/(n+'.template.lean')).read_text();t+='\n'+''.join('set_option pp.all true in\n#check @'+x+'\n#print axioms '+x+'\n'for x in a)
p=S/('source-root/ShielddSecurity/'+n+'.lean');p.parent.mkdir(parents=True);require(len(t.encode())<=262144,'finite source');p.write_text(t)
put('generation01.json',dict(outputs=[dict(name=n,source=pin(p),audits=a)],generator=pin(Path(__file__)),template=pin(S/(n+'.template.lean')),scope='SOURCE-only symbolic body projection. Generic arithmetic satisfaction is internal composition premise and still must be derived from actual indexed full relation by finite leaves; copyCheck also requires qualified instances. No final global/path/hash claim.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(pin(p))
