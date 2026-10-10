from pathlib import Path
import hashlib,json,sys,re
S=Path(__file__).resolve().parent

def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def lin(x):return '['+','.join(f'({c},{v})'for c,v in x)+']'
def emit(n,t):
 t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M));p=S/'source-root/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as f:f.write(t.encode())
 return pin(p)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags');D=S/'selected-data01.json';require(pin(D)['sha256']=='ba23e53b6002643fb22bd73e1944f1c6f696485b814b56ddb1007de064309726','DATA pin');d=json.loads(D.read_bytes());n='MerklePath33AnchorData'
t=f'''import ShielddSecurity.MerkleFamily32Tables
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.{n}
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def output : Linear := {lin(d['result'])}
def anchor : Row := ⟨{lin(d['actual_row']['a'])},[]⟩
theorem output_exact : MerkleFamily32Tables.resultList[14]?.getD []=output := by decide +kernel
theorem anchor_checked : checkRow p [anchor] ⟨subtract output [(4,1)],[]⟩=true := by decide +kernel
theorem reverse_checked : checkOriginalCoverage p 0 #[anchor] #[⟨subtract output [(4,1)],[]⟩] #[0]=true := by decide +kernel
end ShielddSecurity.{n}
'''
sources=[emit(n,t),emit('MerklePath33Meaning',(S/'template.lean').read_text())]
with(S/'generation01.json').open('x')as f:json.dump(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),extractor=pin(S/'extract.py'),data=pin(D),sources=sources),f,sort_keys=True)
print([(x['bytes'],x['sha256'])for x in sources])
