from pathlib import Path
import json,sys
D=json.loads((Path(__file__).resolve().parent/'data.json').read_text());out=(Path(sys.argv[1])/'source-root/ShielddSecurity');out.mkdir(parents=True,exist_ok=True)
lc=lambda x:'['+','.join(f'({c},{v})'for c,v in x)+']'
for entry in D['calls']:
 ci=entry['index'];call=entry['call'];w=call['width'];domain=call['domain'];arity=call['arity'];name=f'AuthorizationHash530C{ci}';blocks=len(call['permutations']);last=blocks-1
 s=''.join(f'import ShielddSecurity.AuthorizationPermutation529C{ci}B{bi}\n'for bi in range(blocks))+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def inputs : List Linear := ['''+','.join(lc(x)for x in entry['inputs'])+f''']
def result := AuthorizationPermutation529C{ci}B{last}.result
def parameters := AuthorizationPermutation529C{ci}B0.parameters
variable {{F : Type}} [Field F] [CharP F p]
def values (rho : Nat → F) := inputs.map (eval rho)
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (AuthorizationPermutation529C{ci}B0.before i))=
      Poseidon.absorb (Poseidon.initial {domain} {arity}) ('''+('(values rho).take 5'if blocks==2 else'values rho')+''') := by
  funext i
  have cases : '''+' ∨ '.join(f'i=⟨{i},by decide⟩'for i in range(w))+''' := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with '''+'|'.join(['rfl']*w)+f''' <;>
    simp [AuthorizationPermutation529C{ci}B0.before,AuthorizationPoseidonCapture518C{ci}B0R00.before,
      Poseidon.absorb,Poseidon.initial,values,inputs,eval,one,Fin.val_ofNat]
'''
 audits=['initial']
 if blocks==2:
  endState=next(x['after']for x in D['phases']if x['call']==ci and x['block']==0 and x['round']==64)
  s+='def endOfFirst : Poseidon.State Linear 6 := fun i => (Array.mk ['+','.join(lc(x)for x in endState)+']).getD i.val []\n'
  s+=f'''theorem endOfFirst_checked : AuthorizationPermutation529C{ci}B0.after=endOfFirst := by
  funext i
  have cases : i=⟨0,by decide⟩ ∨ i=⟨1,by decide⟩ ∨ i=⟨2,by decide⟩ ∨ i=⟨3,by decide⟩ ∨ i=⟨4,by decide⟩ ∨ i=⟨5,by decide⟩ := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
'''
  audits+=['endOfFirst_checked']
  s+=f'''theorem continuation (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (AuthorizationPermutation529C{ci}B1.before i))=
      Poseidon.absorb (fun i => eval rho (AuthorizationPermutation529C{ci}B0.after i)) ((values rho).drop 5) := by
  rw [endOfFirst_checked]
  funext i
  have cases : i=⟨0,by decide⟩ ∨ i=⟨1,by decide⟩ ∨ i=⟨2,by decide⟩ ∨ i=⟨3,by decide⟩ ∨ i=⟨4,by decide⟩ ∨ i=⟨5,by decide⟩ := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [AuthorizationPermutation529C{ci}B1.before,AuthorizationPoseidonCapture518C{ci}B1R00.before,
      endOfFirst,
      Poseidon.absorb,values,inputs,eval,one,Fin.val_ofNat] <;> ring
''';audits+=['continuation']
 s+=f'''theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash{w} (Poseidon.castParameters parameters) {domain} (values rho) := by
'''
 if blocks==1:s+=f'''  have out := AuthorizationPermutation529C{ci}B0.output rho one linked arithmetic
  rw [initial rho one] at out
  exact out
'''
 else:s+=f'''  have first := AuthorizationPermutation529C{ci}B0.permutation rho one linked arithmetic
  rw [initial rho one] at first
  have second := AuthorizationPermutation529C{ci}B1.output rho one linked arithmetic
  rw [continuation rho one,first] at second
  exact second
'''
 s+=f'end ShielddSecurity.{name}\n';audits+=['hash']
 for n in audits:s+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (out/(name+'.lean')).write_text(s)
print('Prepared three source-ordered hash interfaces')

(out/'AuthorizationHashes530.lean').write_text('import ShielddSecurity.AuthorizationHash530C55\nimport ShielddSecurity.AuthorizationHash530C56\nimport ShielddSecurity.AuthorizationHash530C57\nnamespace ShielddSecurity.AuthorizationHashes530\ndef callCount : Nat := 3\nend ShielddSecurity.AuthorizationHashes530\nset_option pp.all true in\n#check @ShielddSecurity.AuthorizationHashes530.callCount\n#print axioms ShielddSecurity.AuthorizationHashes530.callCount\n')
