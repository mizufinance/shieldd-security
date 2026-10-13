import ShielddSecurity.AuthorizationNarrowComposition524
import ShielddSecurity.AuthorizationPrefixBindings527C57B0R00
import ShielddSecurity.AuthorizationPrefixBindings527C57B0R01
import ShielddSecurity.AuthorizationPoseidonRounds528
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPermutation529C57B0
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def parameters := AuthorizationPoseidonCapture518C57B0R00.parameters
def before := AuthorizationPoseidonCapture518C57B0R00.before
def after := AuthorizationNarrowComposition524.after 64
def result : Linear := [(61920,14489116502293865465195620705098702569149962166993518933952339786917836503875),(61924,13125423966940654332711887575940116829944663267413330181877013057693186361539),(61928,37781904496949962127477230973432217892379931214289750852498713884075794707207)]
theorem result_port : after 1=result := by decide +kernel
theorem prefix_seam : AuthorizationPoseidonCapture518C57B0R01.before=AuthorizationPoseidonCapture518C57B0R00.after := rfl
variable {F : Type} [Field F] [CharP F p]
theorem permutation (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after i))=Poseidon.permute (Poseidon.castParameters parameters)
      (fun i => eval rho (before i)) := by
  have first := AuthorizationPrefixBindings527C57B0R00.arbitrary_round rho one linked arithmetic
  have second := AuthorizationPrefixBindings527C57B0R01.arbitrary_round rho one linked arithmetic
  rw [prefix_seam,first] at second
  have result := AuthorizationNarrowComposition524.suffix rho one linked arithmetic
  rw [second] at result
  exact result.trans (AuthorizationPoseidonRounds528.permutation_bridge _ _)
theorem output (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.permute (Poseidon.castParameters parameters) (fun i => eval rho (before i)) 1 := by
  have value := congrFun (permutation rho one linked arithmetic) 1
  rw [result_port] at value
  exact value
end ShielddSecurity.AuthorizationPermutation529C57B0
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C57B0.result_port
#print axioms ShielddSecurity.AuthorizationPermutation529C57B0.result_port
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C57B0.prefix_seam
#print axioms ShielddSecurity.AuthorizationPermutation529C57B0.prefix_seam
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C57B0.permutation
#print axioms ShielddSecurity.AuthorizationPermutation529C57B0.permutation
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPermutation529C57B0.output
#print axioms ShielddSecurity.AuthorizationPermutation529C57B0.output
