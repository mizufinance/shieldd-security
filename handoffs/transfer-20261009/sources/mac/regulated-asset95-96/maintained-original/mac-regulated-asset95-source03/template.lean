import ShielddSecurity.CapturedGlobalSubgroup90
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegulatedAsset95
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def arithmeticRows : List Row := @AR@
def actualRows : List Row := @AS@
def normalizedRows : List Row := [⟨[(32244,-1)],[]⟩]
noncomputable def arithmeticCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9506 2 arithmeticRows
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel
noncomputable def assertionCheck : Bool := CompilerRowSlice63.check CapturedFullRelation58.rowAt 178118 1 actualRows
theorem assertion_checked : assertionCheck=true := by decide +kernel
noncomputable def productCheck : Bool := checkRow p arithmeticRows ⟨subtract [(10,1)] [(6,1),(11,-1)],[(32245,1)]⟩ &&
  checkRow p arithmeticRows ⟨[(10,1)]++[(6,1),(11,-1)],[(32245,1)]++scaleLinear 4 [(32244,1)]⟩
theorem product_checked : productCheck=true := by decide +kernel
noncomputable def reverseCheck : Bool := CompilerIndexed01.checkOriginalCoverage p 0
  actualRows.toArray normalizedRows.toArray (List.range actualRows.length).toArray
theorem reverse_checked : reverseCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 32244=rho 10*(rho 6-rho 11) := by
  have sat:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9506 2
    arithmeticRows arithmetic_checked (by decide) rho arithmetic
  have h:=checked_product_sound rho arithmeticRows [(10,1)] [(6,1),(11,-1)] [(32244,1)] [(32245,1)]
    four_ne_zero sat (Bool.and_eq_true_iff.mp product_checked).1 (Bool.and_eq_true_iff.mp product_checked).2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,sub_eq_add_neg] using h
omit [CharP F p] in
theorem legal_product (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.RegistrySem c w)
    (rho : Nat → F) (asset : rho 6=(w.asset:F)) (registry : rho 11=(w.registry.value:F))
    (regulated : rho 10=(if w.regulated then 1 else 0)) : rho 10*(rho 6-rho 11)=0 := by
  rw [asset,registry,regulated]
  cases flag : w.regulated
  · simp only [Bool.false_eq_true,if_false,zero_mul]
  · have branch:=legal.2.2.2.2.2.2.2.2.2.2
    simp only [flag,if_true] at branch
    rw [branch.1,sub_self,mul_zero]
theorem legal_assertion (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.RegistrySem c w)
    (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (asset : rho 6=(w.asset:F)) (registry : rho 11=(w.registry.value:F))
    (regulated : rho 10=(if w.regulated then 1 else 0)) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 := by
  have zero : rho 32244=0 := (value rho arithmetic).trans (legal_product c w legal rho asset registry regulated)
  have normal : Satisfies rho normalizedRows := by
    intro row member
    have same : row=⟨[(32244,-1)],[]⟩ := by simpa only [normalizedRows,List.mem_singleton] using member
    subst row
    change Square (eval rho [(32244,-1)]) (eval rho [])
    simp only [eval,zero,Int.cast_neg,Int.cast_one,mul_zero,add_zero,Square,zero_mul]
  exact (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 178118 1 actualRows assertion_checked rho).mp
    (transfer rho actualRows normalizedRows reverse_checked normal)
end ShielddSecurity.CapturedRegulatedAsset95
