import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.MerklePath33AnchorData
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CapturedAnchorRowSound165
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
theorem recipe_exact : CapturedFullAssertions54.recipeAt 163=
    some (true,.linear MerklePath33AnchorData.output [(4,1)]) := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem anchor_value (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    eval rho MerklePath33AnchorData.output=rho 4 := by
  have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2
  have row:=truth 163 (by decide) (true,.linear MerklePath33AnchorData.output [(4,1)]) recipe_exact
  change eval rho MerklePath33AnchorData.output=eval rho [(4,1)] at row
  simpa only [eval,Int.cast_one,one_mul,add_zero] using row
end ShielddSecurity.CapturedAnchorRowSound165

set_option pp.all true in
#check @ShielddSecurity.CapturedAnchorRowSound165.recipe_exact
#print axioms ShielddSecurity.CapturedAnchorRowSound165.recipe_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedAnchorRowSound165.anchor_value
#print axioms ShielddSecurity.CapturedAnchorRowSound165.anchor_value
