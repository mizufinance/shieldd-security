import ShielddSecurity.CapturedValueDecode158
import ShielddSecurity.CapturedAssetDecode160
import ShielddSecurity.CapturedNextDecode161
import ShielddSecurity.CapturedRegistryGapSound156
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryOrderSound162
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem meanings (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    CapturedRegistryGapSound156.Meanings rho (CapturedValueDecode158.value rho)
      (CapturedAssetDecode160.value rho) (CapturedNextDecode161.value rho) := by
  have valueBits : ∀ index<255,rho (216+index)=if (encodeBits 255 (CapturedValueDecode158.value rho))[index]?.getD false then 1 else 0 := by
    intro index bound
    simpa only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left] using
      CapturedValueDecode158.bits rho (CapturedValueDecode158.range_truth rho satisfied) index bound
  have assetBits : ∀ index<255,rho (471+index)=if (encodeBits 255 (CapturedAssetDecode160.value rho))[index]?.getD false then 1 else 0 := by
    intro index bound
    simpa only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left] using
      CapturedAssetDecode160.bits rho (CapturedAssetDecode160.range_truth rho satisfied) index bound
  have nextBits : ∀ index<255,rho (726+index)=if (encodeBits 255 (CapturedNextDecode161.value rho))[index]?.getD false then 1 else 0 := by
    intro index bound
    simpa only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left] using
      CapturedNextDecode161.bits rho (CapturedNextDecode161.range_truth rho satisfied) index bound
  exact ⟨HighBitMeaning122.high_meaning rho 471 _ (CapturedAssetDecode160.finite rho) assetBits,
    HighBitMeaning122.high_meaning rho 216 _ (CapturedValueDecode158.finite rho) valueBits,
    LowBitMeaning128.low_meaning rho 471 _ assetBits,LowBitMeaning128.low_meaning rho 216 _ valueBits,
    HighBitMeaning122.high_meaning rho 726 _ (CapturedNextDecode161.finite rho) nextBits,
    LowBitMeaning128.low_meaning rho 726 _ nextBits⟩
theorem canonical_originals (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) :
    (CapturedValueDecode158.value rho<p ∧ (CapturedValueDecode158.value rho:F)=rho 11) ∧
    (CapturedAssetDecode160.value rho<p ∧ (CapturedAssetDecode160.value rho:F)=rho 6) ∧
    (CapturedNextDecode161.value rho<p ∧ (CapturedNextDecode161.value rho:F)=rho 13) :=
  ⟨CapturedValueDecode158.canonical rho satisfied one,CapturedAssetDecode160.canonical rho satisfied one,
    CapturedNextDecode161.canonical rho satisfied one⟩
theorem unregulated (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) (role : rho 10=0) :
    CapturedValueDecode158.value rho<CapturedAssetDecode160.value rho ∧
    CapturedAssetDecode160.value rho<CapturedNextDecode161.value rho := by
  have originals:=canonical_originals rho satisfied one
  exact CapturedRegistryGapSound156.unregulated_sound rho satisfied one role _ _ _
    originals.1.1 originals.2.1.1 originals.2.2.1 (meanings rho satisfied)
end ShielddSecurity.CapturedRegistryOrderSound162

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryOrderSound162.meanings
#print axioms ShielddSecurity.CapturedRegistryOrderSound162.meanings
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryOrderSound162.canonical_originals
#print axioms ShielddSecurity.CapturedRegistryOrderSound162.canonical_originals
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryOrderSound162.unregulated
#print axioms ShielddSecurity.CapturedRegistryOrderSound162.unregulated
