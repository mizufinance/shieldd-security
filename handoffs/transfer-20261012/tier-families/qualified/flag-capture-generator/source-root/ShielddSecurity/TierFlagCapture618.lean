-- GENERATED from gates.json. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagCapture618
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
def same01Rows : List Row := [⟨[(7597,1),(7599,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108447,1)]⟩,⟨[(7597,1),(7599,1)],[(108446,4),(108447,1)]⟩]
theorem same01_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85708 2 same01Rows=true := by decide +kernel
theorem same01_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108446=eval rho [(7597,1)] * eval rho [(7599,1)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85708 2 same01Rows same01_checked (by decide) rho arithmetic
  have result := checked_product_sound rho same01Rows [(7597,1)] [(7599,1)]
    [(108446,1)] [(108447,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def same012Rows : List Row := [⟨[(7601,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108446,1)],[(108453,1)]⟩,⟨[(7601,1),(108446,1)],[(108452,4),(108453,1)]⟩]
theorem same012_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85714 2 same012Rows=true := by decide +kernel
theorem same012_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108452=eval rho [(108446,1)] * eval rho [(7601,1)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85714 2 same012Rows same012_checked (by decide) rho arithmetic
  have result := checked_product_sound rho same012Rows [(108446,1)] [(7601,1)]
    [(108452,1)] [(108453,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def same0123Rows : List Row := [⟨[(7603,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108452,1)],[(108459,1)]⟩,⟨[(7603,1),(108452,1)],[(108458,4),(108459,1)]⟩]
theorem same0123_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85720 2 same0123Rows=true := by decide +kernel
theorem same0123_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108458=eval rho [(108452,1)] * eval rho [(7603,1)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85720 2 same0123Rows same0123_checked (by decide) rho arithmetic
  have result := checked_product_sound rho same0123Rows [(108452,1)] [(7603,1)]
    [(108458,1)] [(108459,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def regulatedExternalRows : List Row := [⟨[(10,1),(108458,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108461,1)]⟩,⟨[(10,1),(108458,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[(108460,4),(108461,1)]⟩]
theorem regulatedExternal_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85722 2 regulatedExternalRows=true := by decide +kernel
theorem regulatedExternal_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108460=eval rho [(10,1)] * eval rho [(200692,1),(108458,-1)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85722 2 regulatedExternalRows regulatedExternal_checked (by decide) rho arithmetic
  have result := checked_product_sound rho regulatedExternalRows [(10,1)] [(200692,1),(108458,-1)]
    [(108460,1)] [(108461,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def eligibleRows : List Row := [⟨[(7607,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108460,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)],[(108483,1)]⟩,⟨[(7607,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108460,1),(200692,2)],[(108482,4),(108483,1)]⟩]
theorem eligible_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85744 2 eligibleRows=true := by decide +kernel
theorem eligible_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108482=eval rho [(200692,2),(7607,-1)] * eval rho [(108460,1)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85744 2 eligibleRows eligible_checked (by decide) rho arithmetic
  have result := checked_product_sound rho eligibleRows [(200692,2),(7607,-1)] [(108460,1)]
    [(108482,1)] [(108483,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def flaggedRows : List Row := [⟨[(7605,1),(108482,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108487,1)]⟩,⟨[(7605,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108482,1),(200692,1)],[(108486,4),(108487,1)]⟩]
theorem flagged_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85748 2 flaggedRows=true := by decide +kernel
theorem flagged_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108486=eval rho [(108482,1)] * eval rho [(200692,1),(7605,-1)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85748 2 flaggedRows flagged_checked (by decide) rho arithmetic
  have result := checked_product_sound rho flaggedRows [(108482,1)] [(200692,1),(7605,-1)]
    [(108486,1)] [(108487,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
theorem polynomial (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108486=(2*rho copy-rho 7607)*rho 10*
      (rho copy-rho 7597*rho 7599*rho 7601*rho 7603)*(rho copy-rho 7605) := by
  change rho 108486=(2*rho 200692-rho 7607)*rho 10*
    (rho 200692-rho 7597*rho 7599*rho 7601*rho 7603)*(rho 200692-rho 7605)
  have flagged := flagged_value rho arithmetic
  have eligible := eligible_value rho arithmetic
  have regulatedExternal := regulatedExternal_value rho arithmetic
  have same0123 := same0123_value rho arithmetic
  have same012 := same012_value rho arithmetic
  have same01 := same01_value rho arithmetic
  simp only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_mul] at same01 same012 same0123 regulatedExternal eligible flagged
  rw [flagged,eligible,regulatedExternal,same0123,same012,same01]
  ring
end ShielddSecurity.TierFlagCapture618

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.same01_checked
#print axioms ShielddSecurity.TierFlagCapture618.same01_checked

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.same01_value
#print axioms ShielddSecurity.TierFlagCapture618.same01_value

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.same012_checked
#print axioms ShielddSecurity.TierFlagCapture618.same012_checked

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.same012_value
#print axioms ShielddSecurity.TierFlagCapture618.same012_value

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.same0123_checked
#print axioms ShielddSecurity.TierFlagCapture618.same0123_checked

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.same0123_value
#print axioms ShielddSecurity.TierFlagCapture618.same0123_value

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.regulatedExternal_checked
#print axioms ShielddSecurity.TierFlagCapture618.regulatedExternal_checked

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.regulatedExternal_value
#print axioms ShielddSecurity.TierFlagCapture618.regulatedExternal_value

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.eligible_checked
#print axioms ShielddSecurity.TierFlagCapture618.eligible_checked

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.eligible_value
#print axioms ShielddSecurity.TierFlagCapture618.eligible_value

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.flagged_checked
#print axioms ShielddSecurity.TierFlagCapture618.flagged_checked

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.flagged_value
#print axioms ShielddSecurity.TierFlagCapture618.flagged_value

set_option pp.all true in
#check @ShielddSecurity.TierFlagCapture618.polynomial
#print axioms ShielddSecurity.TierFlagCapture618.polynomial
