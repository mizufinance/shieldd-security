from pathlib import Path
import sys,hashlib,json,re
S=Path(__file__).resolve().parent
def require(ok,message):
 if not ok:raise ValueError(message)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags before source load')
require(not(S/'producer-manifest01.json').exists()and not(S/'generation01.json').exists(),'no sealed refresh')
template=(S/'template.lean').read_bytes()
require(hashlib.sha256(template).hexdigest()=='d30f34f2063f6da5bbca670db4a758e492c8d6c8b63906ae523417aa10cb3707','exact maintained template')
names=re.findall(r'^(?:noncomputable )?(?:inductive|structure|def|theorem) ([A-Za-z0-9_]+)',template.decode(),re.M)
require(len(names)==17 and len(set(names))==17,'closed public declaration inventory')
source=template+b'\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerAssertionBlock51.{name}\n#print axioms ShielddSecurity.CompilerAssertionBlock51.{name}\n'for name in names).encode()
require(len(source)<=262144,'source cap')
p=S/'source-root/ShielddSecurity/CompilerAssertionBlock51.lean';p.parent.mkdir(parents=True,exist_ok=True)
with p.open('xb')as f:f.write(source)
with(S/'generation01.json').open('x')as f:json.dump(dict(template_sha256=hashlib.sha256(template).hexdigest(),generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_sha256=hashlib.sha256(source).hexdigest(),source_bytes=len(source),audits=['ShielddSecurity.CompilerAssertionBlock51.'+n for n in names],scope='Generic exact row/source-expression equivalence; independent source evaluation and legal-input truth are separate obligations.'),f,sort_keys=True)
