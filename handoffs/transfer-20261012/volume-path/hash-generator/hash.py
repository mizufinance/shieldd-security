import gzip
from pathlib import Path
import json,sys
root=Path(__file__).resolve().parent;d=json.loads(gzip.decompress((root/'data.json.gz').read_bytes()));out=Path(sys.argv[1])/'source-root/ShielddSecurity';out.mkdir(parents=True)
lc=lambda xs:'['+','.join(f'({c},{v})' for c,v in xs)+']'
for call in d['calls']:
 ci=call['index'];domain=call['call']['domain'];arity=call['call']['arity'];inputs=call['inputs'];assert 3<=arity<=5
 phase=next(x for x in d['phases'] if x['call']==ci and x['round']==0);assert phase['before']==[[[0,arity*256+domain]]]+inputs+[[]]*(5-arity)
 perm=f'VolumePathHashPermutation930C{ci}';name=f'VolumePathHash931C{ci}';values='['+','.join('eval rho '+lc(x) for x in inputs)+']'
 s=f"""import ShielddSecurity.{perm}
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def parameters := {perm}.parameters
def result := {perm}.result
def inputs : List Linear := [{','.join(lc(x) for x in inputs)}]
variable {{F : Type}} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho ({perm}.before i))=Poseidon.absorb (Poseidon.initial {domain} {arity}) (inputs.map (eval rho)) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,{arity*256+domain})]=(({arity*256+domain}:Nat):F)
    norm_num [eval,one]
"""
 for x in inputs:s+=f'  · change eval rho {lc(x)}=0+eval rho {lc(x)}\n    exact (zero_add _).symm\n'
 for _ in range(5-arity):s+='  · change (0:F)=0+0\n    exact (add_zero _).symm\n'
 s+=f"""theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) {domain} (inputs.map (eval rho)) := by
  have permutation := {perm}.permutation rho one linked arithmetic
  rw [initial rho one] at permutation
  have joined := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) {domain} (inputs.map (eval rho))
    (Poseidon.initial {domain} {arity}) (fun i => eval rho ({perm}.after i)) rfl rfl permutation
  simpa only [{perm}.result_port,result] using joined
end ShielddSecurity.{name}
"""
 for n in ['initial','hash']:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (out/(name+'.lean')).write_text(s)
