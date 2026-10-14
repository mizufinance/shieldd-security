/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.MapAssetHashComposition737
import ShielddSecurity.MapAssetHashPrefix735C186B0R00
import ShielddSecurity.MapAssetHashPrefix735C186B0R01
import ShielddSecurity.AuthorizationPoseidonRounds528
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashPermutation738
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := MapAssetHashCapture734C186B0R00.parameters
noncomputable def before := MapAssetHashCapture734C186B0R00.before
noncomputable def after := MapAssetHashComposition737.after 64
noncomputable def result : Linear := [(189633,14489116502293865465195620705098702569149962166993518933952339786917836503875),(189637,13125423966940654332711887575940116829944663267413330181877013057693186361539),(189641,37781904496949962127477230973432217892379931214289750852498713884075794707207)]
theorem result_port : after 1=result := by decide +kernel
theorem prefix_seam : MapAssetHashCapture734C186B0R01.before=MapAssetHashCapture734C186B0R00.after := rfl
variable {F : Type} [Field F] [CharP F p]
theorem permutation (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after i))=Poseidon.permute (Poseidon.castParameters parameters)
      (fun i => eval rho (before i)) := by
  have first := MapAssetHashPrefix735C186B0R00.arbitrary_round rho one linked arithmetic
  have second := MapAssetHashPrefix735C186B0R01.arbitrary_round rho one linked arithmetic
  rw [prefix_seam,first] at second
  have result := MapAssetHashComposition737.suffix rho one linked arithmetic
  rw [second] at result
  exact result.trans (AuthorizationPoseidonRounds528.permutation_bridge _ _)
theorem output (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.permute (Poseidon.castParameters parameters) (fun i => eval rho (before i)) 1 := by
  have value := congrFun (permutation rho one linked arithmetic) 1
  rw [result_port] at value
  exact value
end ShielddSecurity.MapAssetHashPermutation738
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashPermutation738.result_port
#print axioms ShielddSecurity.MapAssetHashPermutation738.result_port
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashPermutation738.prefix_seam
#print axioms ShielddSecurity.MapAssetHashPermutation738.prefix_seam
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashPermutation738.permutation
#print axioms ShielddSecurity.MapAssetHashPermutation738.permutation
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashPermutation738.output
#print axioms ShielddSecurity.MapAssetHashPermutation738.output
