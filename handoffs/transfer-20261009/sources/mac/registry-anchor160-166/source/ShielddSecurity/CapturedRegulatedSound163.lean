import ShielddSecurity.CapturedRegistryOrderSound162
import ShielddSecurity.CapturedRegulatedAsset95
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegulatedSound163
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem role_cases (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    rho 10=0 ∨ rho 10=1 := by
  have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2
  have row:=truth 0 (by decide) (true,.square [(10,1)] [(10,1)]) (by rfl)
  change Square (eval rho [(10,1)]) (eval rho [(10,1)]) at row
  have boolean : Square (rho 10) (rho 10) := by simpa only [eval,Int.cast_one,one_mul,add_zero] using row
  exact boolean_sound (rho 10) boolean
theorem pivot_zero (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : rho 32244=0 := by
  have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2
  have row:=truth 164 (by decide) (true,.linear [] [(32244,1)]) (by rfl)
  change eval rho []=eval rho [(32244,1)] at row
  simpa only [eval,Int.cast_one,one_mul,add_zero] using row.symm
theorem product_zero (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    rho 10*(rho 6-rho 11)=0 :=
  (CapturedRegulatedAsset95.value rho ((CapturedFullRelation58.satisfies_split rho).mp satisfied).1).symm.trans (pivot_zero rho satisfied)
theorem regulated_equal (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) (regulated : rho 10=1) : CapturedAssetDecode160.value rho=CapturedValueDecode158.value rho := by
  have asset:=CapturedAssetDecode160.canonical rho satisfied one
  have value:=CapturedValueDecode158.canonical rho satisfied one
  have zero:=product_zero rho satisfied
  rw [regulated,one_mul] at zero
  have equal : rho 6=rho 11 := sub_eq_zero.mp zero
  have casts : (CapturedAssetDecode160.value rho:F)=(CapturedValueDecode158.value rho:F) := asset.2.trans (equal.trans value.2.symm)
  exact CapturedEpochHints62.cast_small_unique _ _ asset.1 value.1 casts
end ShielddSecurity.CapturedRegulatedSound163

set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedSound163.role_cases
#print axioms ShielddSecurity.CapturedRegulatedSound163.role_cases
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedSound163.pivot_zero
#print axioms ShielddSecurity.CapturedRegulatedSound163.pivot_zero
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedSound163.product_zero
#print axioms ShielddSecurity.CapturedRegulatedSound163.product_zero
set_option pp.all true in
#check @ShielddSecurity.CapturedRegulatedSound163.regulated_equal
#print axioms ShielddSecurity.CapturedRegulatedSound163.regulated_equal
