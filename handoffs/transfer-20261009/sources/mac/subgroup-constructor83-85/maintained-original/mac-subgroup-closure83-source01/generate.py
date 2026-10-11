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
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==4,'complete4 declarations')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerSubgroupClosure83.{n}\n#print axioms ShielddSecurity.CompilerSubgroupClosure83.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CompilerSubgroupClosure83.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),qualified_capture_association='TransferFirstSubgroupData01.captureIndices and exact FullRelation58 rowAt; new finite equality checks UNRUN',source=pin(p),audits=['ShielddSecurity.CompilerSubgroupClosure83.'+n for n in names],scope='SOURCE UNRUN. Algebraic double-curve closure and trace nonzero denominator derivation;  Actual first64 arithmetic positions, six deferred subgroup assertions and shared copy selected in full200770-row representation. Arbitrary full satisfaction derives actual preimage curve and three computed affine doubles. Actual Mathlib/native correspondence, other groups and full independent legal constructor remain OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
