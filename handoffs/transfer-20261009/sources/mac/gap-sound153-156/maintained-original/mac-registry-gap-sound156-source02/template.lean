import ShielddSecurity.CapturedFullComparison152
import ShielddSecurity.CapturedNextHighSound153
import ShielddSecurity.CapturedNextLowSound154
import ShielddSecurity.CapturedZeroFlagSound155
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGapSound156
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
def Meanings (rho : Nat → F) (value asset next : Nat) : Prop :=
  fieldBinary (CapturedRegistryHighLimb120.leftColumns.map rho)=((asset/2^128:Nat):F) ∧
  fieldBinary (CapturedRegistryHighLimb120.rightColumns.map rho)=((value/2^128:Nat):F) ∧
  fieldBinary (CapturedRegistryLowLimb129.leftColumns.map rho)=(LowBitMeaning128.low asset:F) ∧
  fieldBinary (CapturedRegistryLowLimb129.rightColumns.map rho)=(LowBitMeaning128.low value:F) ∧
  fieldBinary (CapturedNextHighLimb133.leftColumns.map rho)=((next/2^128:Nat):F) ∧
  fieldBinary (CapturedNextLowLimb140.leftColumns.map rho)=(LowBitMeaning128.low next:F)
theorem next_high_block (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    SatisfiesAt rho CapturedNextHighLimb133.block.actual 130 := by
  intro index bound row found
  apply satisfied (179157+index) (by omega) row
  rw [CapturedNextHighLimb133.full_position index bound]
  exact found
theorem next_low_block (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    SatisfiesAt rho CapturedNextLowLimb140.block.actual 131 := by
  intro index bound row found
  apply satisfied (179290+index) (by omega) row
  rw [CapturedNextLowLimb140.full_position index bound]
  exact found
variable [CharP F p]
theorem first_le (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) (value asset next : Nat) (valueBound : value<2^255) (assetBound : asset<2^255)
    (meanings : Meanings rho value asset next) :
    (1-rho 981)*(1-rho 1110*rho 1112)=(if asset≤value then (1:F) else 0) := by
  have high:=CapturedFullComparison152.high_sound rho satisfied (asset/2^128) (value/2^128)
    (HighBitMeaning122.high_bound asset assetBound) (HighBitMeaning122.high_bound value valueBound) meanings.1 meanings.2.1
  have low:=CapturedFullComparison152.low_sound rho satisfied (LowBitMeaning128.low asset) (LowBitMeaning128.low value)
    (LowBitMeaning128.low_bound asset) (LowBitMeaning128.low_bound value) meanings.2.2.1 meanings.2.2.2.1
  have equal:=CapturedZeroFlagSound155.first_flag rho satisfied one
  rw [CapturedZeroFlagSound155.first_delta rho,meanings.1,meanings.2.1] at equal
  rw [high.1,low.1,equal]
  exact LexicographicComparison144.lex_field asset value assetBound valueBound
theorem next_le (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) (value asset next : Nat) (assetBound : asset<2^255) (nextBound : next<2^255)
    (meanings : Meanings rho value asset next) :
    (1-rho 1242)*(1-rho 1371*rho 1373)=(if next≤asset then (1:F) else 0) := by
  have assetHigh : fieldBinary (CapturedNextHighLimb133.rightColumns.map rho)=((asset/2^128:Nat):F) := meanings.1
  have assetLow : fieldBinary (CapturedNextLowLimb140.rightColumns.map rho)=(LowBitMeaning128.low asset:F) := meanings.2.2.1
  have linked:=(CapturedFullRelation58.verifier_links rho satisfied).2.2
  have high:=CapturedNextHighSound153.sound rho (next/2^128) (asset/2^128)
    (HighBitMeaning122.high_bound next nextBound) (HighBitMeaning122.high_bound asset assetBound)
    meanings.2.2.2.2.1 assetHigh linked (next_high_block rho satisfied)
  have low:=CapturedNextLowSound154.sound rho (LowBitMeaning128.low next) (LowBitMeaning128.low asset)
    (LowBitMeaning128.low_bound next) (LowBitMeaning128.low_bound asset)
    meanings.2.2.2.2.2 assetLow linked (next_low_block rho satisfied)
  have equal:=CapturedZeroFlagSound155.next_flag rho satisfied one
  rw [CapturedZeroFlagSound155.next_delta rho,meanings.2.2.2.2.1,assetHigh] at equal
  rw [high.1,low.1,equal]
  exact LexicographicComparison144.lex_field next asset nextBound assetBound
theorem unregulated_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) (unregulated : rho 10=0) (value asset next : Nat)
    (valueBound : value<p) (assetBound : asset<p) (nextBound : next<p)
    (meanings : Meanings rho value asset next) : value<asset ∧ asset<next := by
  have small : p<2^255 := by decide
  have vb:=Nat.lt_trans valueBound small
  have ab:=Nat.lt_trans assetBound small
  have nb:=Nat.lt_trans nextBound small
  have polynomial:=CapturedFullComparison152.gap_polynomial_zero rho satisfied one
  rw [unregulated,sub_zero,one_mul,first_le rho satisfied one value asset next vb ab meanings,
    next_le rho satisfied one value asset next ab nb meanings] at polynomial
  have first : ¬asset≤value := by
    intro before
    have impossible : (1:F)=0 := by simpa only [if_pos before,sub_self,zero_mul,sub_zero] using polynomial
    exact one_ne_zero impossible
  have second : ¬next≤asset := by
    intro before
    have impossible : (1:F)=0 := by simpa only [if_pos before,sub_self,mul_zero,sub_zero] using polynomial
    exact one_ne_zero impossible
  constructor <;> omega
end ShielddSecurity.CapturedRegistryGapSound156
