from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent;R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');D=R/'work/mac-merkle-family32-data01/selected-data01.json'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def lin(xs):return '['+','.join(f'({c},{v})'for c,v in xs)+']'
def write(p,b):
 if p.exists():require(p.read_bytes()==b,'immutable replay')
 else:
  with p.open('xb')as f:f.write(b)
def cases(body):
 return '  have cases : '+' ∨ '.join(f'i={j}'for j in range(15))+' := by have h := i.isLt;simp only [Fin.ext_iff];omega\n  rcases cases with '+'|'.join(['rfl']*15)+'\n'+''.join('  · '+x+'\n'for x in body)
def table(field,rd,ty):
 return f'def {field}{rd} (i : Fin 15) : {ty} :=\n  match i.val with\n'+''.join(f'  | {j} => MerkleFamily32L{j+2:02d}R{rd}.{field}\n'for j in range(15))+f'  | _ => MerkleFamily32L02R{rd}.{field}\n'
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags');require(pin(D)['sha256']=='54d0de34d64a281643185ec9e85f00cb4ad78e5f992680babd50dd9ed780a03f','data');d=json.loads(D.read_bytes());ns='MerkleFamily32Tables'
t=''.join(f'import ShielddSecurity.MerkleFamily32BindingL{j:02d}\n'for j in range(2,17))+'''import ShielddSecurity.MerkleFamily32Audit
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32Tables
open Compiler Poseidon CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def offset (i : Fin 15) := 424*(i.val+2)
'''
for rd in range(2):
 t+=table('data',rd,'ReusablePoseidonPhase31.Data 6')
 t+=f'theorem certificate{rd} (i : Fin 15) : ReusablePoseidonPhase31.Certificate (data{rd} i) := by\n'+cases([f'exact MerkleFamily32L{j+2:02d}R{rd}.checked'for j in range(15)])
 t+=f'theorem parameters{rd} (i : Fin 15) : (data{rd} i).parameters=TransferPoseidonCall04Shared01.parameters := by\n'+cases(['rfl']*15)
 t+=f'theorem index{rd} (i : Fin 15) : (data{rd} i).index={rd} := by\n'+cases(['rfl']*15)
 low=25048 if rd==0 else 25064;high=25064 if rd==0 else 25088
 t+=f'theorem bounds{rd} (i : Fin 15) : (data{rd} i).low={low}+offset i ∧ (data{rd} i).high={high}+offset i := by\n'+cases(['exact ⟨rfl,rfl⟩']*15)
t+='theorem phase_seam (i : Fin 15) : (data1 i).before=(data0 i).after := by\n'+cases(['rfl']*15)
t+='''def expectedBefore (i : Fin 15) (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,(i.val+2 : Nat))] else
    MerkleFamily32Selection.outputs i ⟨k.val-2,by omega⟩
def resultList : List Linear := '''+'['+','.join(lin(x['result'])for x in d['levels'][1:])+']\n'
t+='''def actualResult (i : Fin 15) := resultList[i.val]?.getD []
def previousResult (i : Fin 15) := if i.val=0 then MerkleHash27Whole.actualResult else resultList[i.val-1]?.getD []
def beforeCheck (i : Fin 15) := (List.finRange 6).all (fun k => decide (canonical p ((data0 i).before k)=canonical p (expectedBefore i k)))
def seamCheck (i : Fin 15) := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before (offset i) k)=canonical p ((data1 i).after k)))
def resultCheck (i : Fin 15) := decide (canonical p (ReusableWideTail25.after (offset i) 1)=canonical p (actualResult i))
def leafCheck (i : Fin 15) := decide (canonical p (MerkleFamily32Selection.leaf i)=canonical p (previousResult i))
'''
for j in range(15):
 t+=f'theorem bindings{j} : beforeCheck {j}=true ∧ seamCheck {j}=true ∧ resultCheck {j}=true ∧ leafCheck {j}=true := MerkleFamily32BindingL{j+2:02d}.checked\n'
t+='theorem bindings (i : Fin 15) : beforeCheck i=true ∧ seamCheck i=true ∧ resultCheck i=true ∧ leafCheck i=true := by\n'+cases([f'exact bindings{j}'for j in range(15)])
t+='''variable {F : Type} [Field F] [CharP F p]
theorem before_values (i : Fin 15) (rho : Nat → F) : (fun k => eval rho ((data0 i).before k))=(fun k => eval rho (expectedBefore i k)) := by
  funext k
  exact canonical_equal (p:=p) rho _ _ (of_decide_eq_true (List.all_eq_true.mp (bindings i).1 k (List.mem_finRange k)))
theorem tail_seam (i : Fin 15) (rho : Nat → F) : (fun k => eval rho (ReusableWideTail25.before (offset i) k))=(fun k => eval rho ((data1 i).after k)) := by
  funext k
  exact canonical_equal (p:=p) rho _ _ (of_decide_eq_true (List.all_eq_true.mp (bindings i).2.1 k (List.mem_finRange k)))
theorem result_values (i : Fin 15) (rho : Nat → F) : eval rho (ReusableWideTail25.after (offset i) 1)=eval rho (actualResult i) :=
  canonical_equal (p:=p) rho _ _ (of_decide_eq_true (bindings i).2.2.1)
theorem leaf_values (i : Fin 15) (rho : Nat → F) : eval rho (MerkleFamily32Selection.leaf i)=eval rho (previousResult i) :=
  canonical_equal (p:=p) rho _ _ (of_decide_eq_true (bindings i).2.2.2)
end ShielddSecurity.MerkleFamily32Tables
'''
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{ns}.{n}\n#print axioms ShielddSecurity.{ns}.{n}\n'for n in re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M));b=t.encode();require(len(b)<=262144,'source');write(S/'source-root/ShielddSecurity'/(ns+'.lean'),b);write(S/'generation01.json',(json.dumps(dict(generator=pin(Path(__file__)),data=pin(D),source=pin(S/'source-root/ShielddSecurity'/(ns+'.lean'))),sort_keys=True)+'\n').encode());print(len(b))
