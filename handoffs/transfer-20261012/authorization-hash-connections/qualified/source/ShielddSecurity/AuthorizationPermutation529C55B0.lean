import ShielddSecurity.AuthorizationWideComposition526C55B0
import ShielddSecurity.AuthorizationPrefixBindings527C55B0R00
import ShielddSecurity.AuthorizationPrefixBindings527C55B0R01
import ShielddSecurity.AuthorizationPoseidonRounds528
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPermutation529C55B0
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def parameters := AuthorizationPoseidonCapture518C55B0R00.parameters
def before := AuthorizationPoseidonCapture518C55B0R00.before
def after := AuthorizationWideComposition526C55B0.after 64
def result : Linear := [(50178,5579934908212736977238010113730457006906792843192217773053283881663622591681),(50182,50978946942794420813356136484142315443152313428221265043903658432145007475423),(50186,51737743277955608982399432577620617083998176562860787771480331520415801857016),(50190,280754542936071555323583947036382301904172335755315562603417507239324752636),(50194,44773762128641970103070913747625047847186741019957383563700055475244115610384),(50198,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
theorem result_port : after 1=result := by decide +kernel
theorem prefix_seam : AuthorizationPoseidonCapture518C55B0R01.before=AuthorizationPoseidonCapture518C55B0R00.after := rfl
variable {F : Type} [Field F] [CharP F p]
theorem permutation (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after i))=Poseidon.permute (Poseidon.castParameters parameters)
      (fun i => eval rho (before i)) := by
  have first := AuthorizationPrefixBindings527C55B0R00.arbitrary_round rho one linked arithmetic
  have second := AuthorizationPrefixBindings527C55B0R01.arbitrary_round rho one linked arithmetic
  rw [prefix_seam,first] at second
  have result := AuthorizationWideComposition526C55B0.suffix rho one linked arithmetic
  rw [second] at result
  exact result.trans (AuthorizationPoseidonRounds528.permutation_bridge _ _)
theorem output (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.permute (Poseidon.castParameters parameters) (fun i => eval rho (before i)) 1 := by
  have value := congrFun (permutation rho one linked arithmetic) 1
  rw [result_port] at value
  exact value
end ShielddSecurity.AuthorizationPermutation529C55B0
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C55B0.result_port
#print axioms ShielddSecurity.AuthorizationPermutation529C55B0.result_port
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C55B0.prefix_seam
#print axioms ShielddSecurity.AuthorizationPermutation529C55B0.prefix_seam
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C55B0.permutation
#print axioms ShielddSecurity.AuthorizationPermutation529C55B0.permutation
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C55B0.output
#print axioms ShielddSecurity.AuthorizationPermutation529C55B0.output
