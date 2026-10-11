import ShielddSecurity.CapturedHighComparisonSound149
import ShielddSecurity.CapturedLowComparisonSound151
import ShielddSecurity.CapturedRegistryGap146
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFullComparison152
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem high_block (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    SatisfiesAt rho CapturedRegistryHighLimb120.block.actual 130 := by
  intro index bound row found
  apply satisfied (178893+index) (by omega) row
  rw [CapturedRegistryHighLimb120.full_position index bound]
  exact found
theorem low_block (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    SatisfiesAt rho CapturedRegistryLowLimb129.block.actual 131 := by
  intro index bound row found
  apply satisfied (179026+index) (by omega) row
  rw [CapturedRegistryLowLimb129.full_position index bound]
  exact found
theorem high_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (a b : Nat) (left : a<2^127) (right : b<2^127)
    (leftMeaning : fieldBinary (CapturedRegistryHighLimb120.leftColumns.map rho)=(a:F))
    (rightMeaning : fieldBinary (CapturedRegistryHighLimb120.rightColumns.map rho)=(b:F)) :
    rho 981=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) ∧
      rho 982=(BoundedLimbComparison119.difference 127 a b:F) :=
  CapturedHighComparisonSound149.sound rho a b left right leftMeaning rightMeaning
    (CapturedFullRelation58.verifier_links rho satisfied).2.2 (high_block rho satisfied)
theorem low_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (a b : Nat) (left : a<2^128) (right : b<2^128)
    (leftMeaning : fieldBinary (CapturedRegistryLowLimb129.leftColumns.map rho)=(a:F))
    (rightMeaning : fieldBinary (CapturedRegistryLowLimb129.rightColumns.map rho)=(b:F)) :
    rho 1112=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) ∧
      rho 1113=(BoundedLimbComparison119.difference 128 a b:F) :=
  CapturedLowComparisonSound151.sound rho a b left right leftMeaning rightMeaning
    (CapturedFullRelation58.verifier_links rho satisfied).2.2 (low_block rho satisfied)
theorem gap_zero (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    rho 33788=0 := by
  let row : Row := ⟨[(33788,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
  have position : CapturedFullRelation58.rowAt 179421=some row :=
    (CapturedRegistryGap146.actual_position 0 (by decide)).trans (by rfl)
  have sat:=satisfied 179421 (by decide) row position
  have checked : checkRow p copy row (true,.linear [(33788,-1)] [])=true := by decide +kernel
  have truth:=(checked_iff copy row (true,.linear [(33788,-1)] []) checked rho
    (CapturedFullRelation58.verifier_links rho satisfied).2.2).mp sat
  change eval rho [(33788,-1)]=eval rho [] at truth
  simpa only [eval,Int.cast_neg,Int.cast_one,neg_one_mul,add_zero,neg_eq_zero] using truth
theorem gap_polynomial_zero (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
    (1-rho 10)*(1-(1-(1-rho 981)*(1-rho 1110*rho 1112))*
      (1-(1-rho 1242)*(1-rho 1371*rho 1373)))=0 := by
  have h:=CapturedRegistryGap145.gap_polynomial rho
    ((CapturedFullRelation58.satisfies_split rho).mp satisfied).1 one
    (CapturedFullRelation58.verifier_links rho satisfied).2.2
  exact h.symm.trans (gap_zero rho satisfied)
end ShielddSecurity.CapturedFullComparison152

set_option pp.all true in
#check @ShielddSecurity.CapturedFullComparison152.high_block
#print axioms ShielddSecurity.CapturedFullComparison152.high_block
set_option pp.all true in
#check @ShielddSecurity.CapturedFullComparison152.low_block
#print axioms ShielddSecurity.CapturedFullComparison152.low_block
set_option pp.all true in
#check @ShielddSecurity.CapturedFullComparison152.high_sound
#print axioms ShielddSecurity.CapturedFullComparison152.high_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedFullComparison152.low_sound
#print axioms ShielddSecurity.CapturedFullComparison152.low_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedFullComparison152.gap_zero
#print axioms ShielddSecurity.CapturedFullComparison152.gap_zero
set_option pp.all true in
#check @ShielddSecurity.CapturedFullComparison152.gap_polynomial_zero
#print axioms ShielddSecurity.CapturedFullComparison152.gap_polynomial_zero
