from pathlib import Path
import json,re,hashlib,sys
S=Path(__file__).resolve().parent;R=S.parent.parent
D=R/'work/mac-merkle-family32-data01/selected-data01.json'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as f:f.write(b)
def lin(xs):return '['+','.join(f'({c},{v})'for c,v in xs)+']'
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
require(pin(D)['sha256']=='54d0de34d64a281643185ec9e85f00cb4ad78e5f992680babd50dd9ed780a03f','data')
d=json.loads(D.read_bytes());records=[]
for i in range(15):
 j=i+2;n=f'MerkleFamily32BindingL{j:02d}';a=f'MerkleFamily32L{j:02d}R0';b=f'MerkleFamily32L{j:02d}R1';off=424*j
 previous='MerkleHash27Whole.actualResult'if i==0 else lin(d['levels'][i]['result'])
 t=f'''import ShielddSecurity.{a}
import ShielddSecurity.{b}
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{n}
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def expectedBefore (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,{j})] else
    MerkleFamily32Selection.outputs {i} ⟨k.val-2,by omega⟩
def actualResult : Linear := {lin(d['levels'][i+1]['result'])}
def previousResult : Linear := {previous}
def beforeCheck := (List.finRange 6).all (fun k => decide (canonical p ({a}.data.before k)=canonical p (expectedBefore k)))
def seamCheck := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before {off} k)=canonical p ({b}.data.after k)))
def resultCheck := decide (canonical p (ReusableWideTail25.after {off} 1)=canonical p actualResult)
def leafCheck := decide (canonical p (MerkleFamily32Selection.leaf {i})=canonical p previousResult)
theorem checked : beforeCheck=true ∧ seamCheck=true ∧ resultCheck=true ∧ leafCheck=true := by decide +kernel
end ShielddSecurity.{n}
'''
 t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M));p=S/'source-root/ShielddSecurity'/(n+'.lean');write(p,t.encode());records.append(pin(p))
write(S/'generation01.json',(json.dumps(dict(generator=pin(Path(__file__)),data=pin(D),sources=records),sort_keys=True)+'\n').encode());print(sum(x['bytes']for x in records))
