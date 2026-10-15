import gzip
from pathlib import Path
import json,sys
D=json.loads(gzip.decompress((Path(__file__).resolve().parent/'data.json.gz').read_bytes()));out=(Path(sys.argv[1])/'source-root/ShielddSecurity');out.mkdir(parents=True,exist_ok=True)
for ci,bi,w in [(call['index'],bi,6) for call in D['calls'] for bi in range(len(call['call']['permutations']))]:
 name=f'UserPathHashPermutation957C{ci}B{bi}';prefix=f'UserPathHashCapture953C{ci}B{bi}';bindings=f'UserPathHashPrefix954C{ci}B{bi}';tail=f'UserPathHashComposition956C{ci}B{bi}';phase=next(x for x in D['phases']if x['call']==ci and x['block']==bi and x['round']==64);lc='['+','.join(f'({c},{v})'for c,v in phase['after'][1])+']'
 s=f'''import ShielddSecurity.{tail}
import ShielddSecurity.{bindings}R00
import ShielddSecurity.{bindings}R01
import ShielddSecurity.AuthorizationPoseidonRounds528
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def parameters := {prefix}R00.parameters
def before := {prefix}R00.before
def after := {tail}.after 64
def result : Linear := {lc}
theorem result_port : after 1=result := by decide +kernel
theorem prefix_seam : {prefix}R01.before={prefix}R00.after := rfl
variable {{F : Type}} [Field F] [CharP F p]
theorem permutation (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after i))=Poseidon.permute (Poseidon.castParameters parameters)
      (fun i => eval rho (before i)) := by
  have first := {bindings}R00.arbitrary_round rho one linked arithmetic
  have second := {bindings}R01.arbitrary_round rho one linked arithmetic
  rw [prefix_seam,first] at second
  have result := {tail}.suffix rho one linked arithmetic
  rw [second] at result
  exact result.trans (AuthorizationPoseidonRounds528.permutation_bridge _ _)
theorem output (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.permute (Poseidon.castParameters parameters) (fun i => eval rho (before i)) 1 := by
  have value := congrFun (permutation rho one linked arithmetic) 1
  rw [result_port] at value
  exact value
end ShielddSecurity.{name}
'''
 for n in ['result_port','prefix_seam','permutation','output']:s+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (out/(name+'.lean')).write_text(s)
print('Prepared four full permutation interfaces')
