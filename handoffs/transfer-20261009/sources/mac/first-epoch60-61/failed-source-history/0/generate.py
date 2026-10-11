from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'generation01.json').exists() and not(S/'source-root').exists(),'immutable emission')
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M)
require(len(names)==16,'complete public declaration inventory')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedEpochRange60.{n}\n#print axioms ShielddSecurity.CapturedEpochRange60.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedEpochRange60.lean'
with p.open('x')as f:f.write(t)
with(S/'generation01.json').open('x')as f:f.write(json.dumps(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),source=pin(p),audits=['ShielddSecurity.CapturedEpochRange60.'+n for n in names],scope='SOURCE only, all sixteen audits UNRUN. First64-bit range: actual assertion positions177979..178043, source input31/column34; only hidden bit columns49..112 updated. Constructor needs independent n<2^64/input cast/copy linkage. No preservation of owned hint input columns, no epoch nonzero/audit protocol/native/full Transfer claim.'),sort_keys=True,separators=(',',':'))+'\n')
print(pin(p))
