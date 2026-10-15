import gzip
from pathlib import Path
import json,sys
root=Path(__file__).resolve().parent;d=json.loads(gzip.decompress((root/'data.json.gz').read_bytes()));out=Path(sys.argv[1])/'source-root/ShielddSecurity';out.mkdir(parents=True)
lc=lambda xs:'['+','.join(f'({c},{v})' for c,v in xs)+']'
for call in d['calls']:
 ci=call['index'];domain=call['call']['domain'];arity=call['call']['arity'];inputs=call['inputs'];blocks=len(call['call']['permutations']);assert (blocks==1 and arity==5) or (blocks==2 and arity==9)
 phase=next(x for x in d['phases'] if x['call']==ci and x['block']==0 and x['round']==0);assert phase['before']==[[[0,arity*256+domain]]]+inputs[:5]
 perm=f'UserPathHashPermutation957C{ci}B0';last=f'UserPathHashPermutation957C{ci}B{blocks-1}';name=f'UserPathHash958C{ci}';first='inputs.map (eval rho)' if blocks==1 else '(inputs.map (eval rho)).take 5'
 s=''.join(f'import ShielddSecurity.UserPathHashPermutation957C{ci}B{bi}\n' for bi in range(blocks))+'import ShielddSecurity.WideHashTwoBlocks960\n'+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def parameters := {perm}.parameters
def result := {last}.result
def inputs : List Linear := [{','.join(lc(x) for x in inputs)}]
variable {{F : Type}} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho ({perm}.before i))=Poseidon.absorb (Poseidon.initial {domain} {arity}) ({first}) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,{arity*256+domain})]=(({arity*256+domain}:Nat):F)
    norm_num [eval,one]
'''
 for x in inputs[:5]:s+=f'  · change eval rho {lc(x)}=0+eval rho {lc(x)}\n    exact (zero_add _).symm\n'
 names=['initial']
 if blocks==2:
  for j in range(6):
   shape=f'{perm}.after {j}'+('++'+lc(inputs[j+4]) if 1<=j<=4 else '')
   s+=f'theorem continuation{j}_shape : canonical p ({last}.before {j})=canonical p ({shape}) := by decide +kernel\n';names.append(f'continuation{j}_shape')
  s+=f'''theorem continuation (rho : Nat → F) :
    (fun i => eval rho ({last}.before i))=Poseidon.absorb (fun i => eval rho ({perm}.after i)) ((inputs.map (eval rho)).drop 5) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho ({last}.before 0)=eval rho ({perm}.after 0)
    exact canonical_equal rho _ _ continuation0_shape
'''
  for j in range(1,5):s+=f'''  · change eval rho ({last}.before {j})=eval rho ({perm}.after {j})+eval rho {lc(inputs[j+4])}
    rw [canonical_equal rho _ _ continuation{j}_shape,eval_append]
'''
  s+=f'''  · change eval rho ({last}.before 5)=eval rho ({perm}.after 5)+0
    rw [canonical_equal rho _ _ continuation5_shape,add_zero]
''';names.append('continuation')
 s+=f'''theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) {domain} (inputs.map (eval rho)) := by
  have first := {perm}.permutation rho one linked arithmetic
  rw [initial rho one] at first
'''
 if blocks==1:
  s+=f'''  have joined := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) {domain} (inputs.map (eval rho))
    (Poseidon.initial {domain} {arity}) (fun i => eval rho ({perm}.after i)) rfl rfl first
'''
 else:
  s+=f'''  have second := {last}.permutation rho one linked arithmetic
  rw [continuation rho] at second
  have joined := WideHashTwoBlocks960.hash (Poseidon.castParameters parameters) {domain} (inputs.map (eval rho))
    ((inputs.map (eval rho)).take 5) ((inputs.map (eval rho)).drop 5) (Poseidon.initial {domain} {arity})
    (fun i => eval rho ({perm}.after i)) (fun i => eval rho ({last}.after i)) rfl rfl first second
'''
 s+=f'  simpa only [{last}.result_port,result] using joined\nend ShielddSecurity.{name}\n';names.append('hash')
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (out/(name+'.lean')).write_text(s)
