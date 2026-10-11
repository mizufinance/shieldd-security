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
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable fresh emission')
require(hashlib.sha256(Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-registry-value-global99-source02/source-root/ShielddSecurity/CapturedRegistryValueGlobal99.lean').read_bytes()).hexdigest()=='c7b6e4ef59035ca2eb74cd368f4d75c0b1fcf923a7dcbf53945f93abf973b41a','exact inherited statement source');t=(S/'template.lean').read_bytes();require(len(t)<262144,'source bound');r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedValueGlobal108.lean';p.write_bytes(t)
put('generation01.json',dict(source=pin(p),template=pin(S/'template.lean'),generator=pin(Path(__file__)),audits=['ShielddSecurity.CapturedValueGlobal108.'+n for n in ['completed', 'bits', 'zero', 'canonical_assertions', 'legal_registry_global422']],scope='One shared legal RegistrySem constructor extends420 with2 actual canonical-value assertions, explicit original roles/preimage/group/field certificates retained. Not full Transfer/native. Maintained original99 theorem statement copied with explicit extra conclusions, no assumed desired truth.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
