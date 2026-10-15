import gzip,json,sys
from pathlib import Path
root=Path(__file__).resolve().parent;d=json.loads(gzip.decompress((root/'data.json.gz').read_bytes()));out=Path(sys.argv[1])/'source-root/ShielddSecurity';out.mkdir(parents=True)
assert len(d['calls'])==1;call=d['calls'][0];assert call['index']==187 and call['call']['domain']==34 and call['call']['arity']==64 and len(call['call']['permutations'])==13
inputs=call['inputs'];lc=lambda xs:'['+','.join(f'({c},{v})' for c,v in xs)+']';perm=lambda i:f'PublicStatementHashPermutation976C187B{i}';name='PublicStatementHash977C187'
phase=next(x for x in d['phases'] if x['call']==187 and x['block']==0 and x['round']==0);assert phase['before']==[[[0,64*256+34]]]+inputs[:5]
s=''.join(f'import ShielddSecurity.{perm(i)}\n' for i in range(13))+'import ShielddSecurity.WideHashBlocks971\n'+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def parameters := {perm(0)}.parameters
def result := {perm(12)}.result
def inputs : List Linear := [{','.join(lc(x) for x in inputs)}]
variable {{F : Type}} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt

def parts (rho : Nat → F) : List (List F) :=
  [{','.join('['+','.join('eval rho '+lc(x) for x in inputs[i:i+5])+']' for i in range(0,64,5))}]

def states (rho : Nat → F) : Nat → Poseidon.State F 6
  | 0 => Poseidon.initial 34 64
'''
for i in range(13):s+=f'  | {i+1} => fun j => eval rho ({perm(i)}.after j)\n'
s+='  | _ => fun _ => 0\n'
s+=f'''theorem chunks (rho : Nat → F) : Poseidon.chunks5 (inputs.map (eval rho))=parts rho := rfl

theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho ({perm(0)}.before i))=Poseidon.absorb (Poseidon.initial 34 64) ((parts rho).get ⟨0,by change 0 < 13; decide⟩) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,{64*256+34})]=(({64*256+34}:Nat):F)
    norm_num [eval,one]
'''
for x in inputs[:5]:s+=f'  · change eval rho {lc(x)}=0+eval rho {lc(x)}\n    exact (zero_add _).symm\n'
names=['chunks','initial']
for i in range(1,13):
 for j in range(6):
  addition=inputs[5*i+j-1] if j and 5*i+j-1<64 else None;shape=f'{perm(i-1)}.after {j}'+('++'+lc(addition) if addition is not None else '')
  s+=f'theorem continuation{i}_{j}_shape : canonical p ({perm(i)}.before {j})=canonical p ({shape}) := by decide +kernel\n';names.append(f'continuation{i}_{j}_shape')
 s+=f'''theorem continuation{i} (rho : Nat → F) :
    (fun j => eval rho ({perm(i)}.before j))=Poseidon.absorb (fun j => eval rho ({perm(i-1)}.after j)) ((parts rho).get ⟨{i},by change {i} < 13; decide⟩) := by
  funext j
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by have h:=j.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho ({perm(i)}.before 0)=eval rho ({perm(i-1)}.after 0)
    exact canonical_equal rho _ _ continuation{i}_0_shape
'''
 for j in range(1,6):
  if 5*i+j-1<64:s+=f'''  · change eval rho ({perm(i)}.before {j})=eval rho ({perm(i-1)}.after {j})+eval rho {lc(inputs[5*i+j-1])}
    rw [canonical_equal rho _ _ continuation{i}_{j}_shape,eval_append]
'''
  else:s+=f'''  · change eval rho ({perm(i)}.before {j})=eval rho ({perm(i-1)}.after {j})+0
    rw [canonical_equal rho _ _ continuation{i}_{j}_shape,add_zero]
'''
 names.append(f'continuation{i}')
s+='''theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 34 (inputs.map (eval rho)) := by
'''
for i in range(13):
 s+=f'  have block{i} := {perm(i)}.permutation rho one linked arithmetic\n'
 s+=f'  rw ['+('initial rho one' if i==0 else f'continuation{i} rho')+f'] at block{i}\n'
s+='''  have advance : ∀ i (inside : i<13), states rho (i+1)=
      Poseidon.permute (Poseidon.castParameters parameters) (Poseidon.absorb (states rho i) (parts rho)[i]) := by
    intro i inside
    match i with
'''
for i in range(13):s+=f'    | {i} => exact block{i}\n'
s+='''    | n+13 => omega
  have joined := WideHashBlocks971.hash (Poseidon.castParameters parameters) 34 (inputs.map (eval rho))
    (parts rho) (states rho) (chunks rho) (by intro h;cases h) rfl advance
'''
s+=f'  simpa only [parts,states,{perm(12)}.result_port,result] using joined\nend ShielddSecurity.{name}\n';names.append('hash')
for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
(out/(name+'.lean')).write_text(s)
