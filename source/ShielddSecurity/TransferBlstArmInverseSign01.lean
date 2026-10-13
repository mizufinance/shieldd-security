import ShielddSecurity.TransferBlstArmSqrtWhile01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSign01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)

/-! Integer interpretation of the original inverse's two signed high-half
adjustments. The exact rx2 words are bound to q<<1. A signed 512-bit coefficient
bound derives unsigned output range and unchanged field residue. Actual
coefficient production, signed word/carry interpretation and native execution
remain separate; no desired inverse or output value is supplied. -/

def sourceRx2 : Vector UInt64 4 :=
  #v[0xfffffffe00000002,0xa77b4805fffcb7fd,0x6673b0101343b00a,0xe7db4ea6533afa90]

theorem original_rx2_words_are_exactly_twice_the_scalar_modulus :
    packWords sourceRx2.toList = 2*nullifierModulus := by decide

def sourceWideRadix : Int := ((radix64^8:Nat):Int)
def sourceCorrectionShift : Int := (packWords sourceRx2.toList:Int)*((radix64^4:Nat):Int)

theorem original_correction_shift_is_between_half_and_whole_wide_radix :
    0<sourceCorrectionShift ∧ sourceCorrectionShift<sourceWideRadix ∧ sourceWideRadix<2*sourceCorrectionShift := by
  decide

def sourceSignedFirst (value : Int) : Int :=
  if value<0 then value+sourceCorrectionShift else value

def sourceSignedCorrection (value : Int) : Int :=
  let first := sourceSignedFirst value
  if first<0 then first+sourceCorrectionShift
  else if sourceWideRadix≤first then first-sourceCorrectionShift else first

theorem original_two_signed_adjustments_derive_unsigned_wide_range
    (value : Int) (lower : -sourceWideRadix≤value) (upper : value≤sourceWideRadix) :
    0≤sourceSignedCorrection value ∧ sourceSignedCorrection value<sourceWideRadix := by
  have bounds := original_correction_shift_is_between_half_and_whole_wide_radix
  dsimp only [sourceSignedCorrection,sourceSignedFirst]
  split_ifs <;> constructor <;> omega

theorem original_correction_shift_has_zero_scalar_field_residue :
    (sourceCorrectionShift : ZMod nullifierModulus)=0 := by decide

attribute [local simp] Int.cast_add Int.cast_sub original_correction_shift_has_zero_scalar_field_residue

theorem original_two_signed_adjustments_retain_the_original_coefficient_field_residue
    (value : Int) : (sourceSignedCorrection value : ZMod nullifierModulus)=(value : ZMod nullifierModulus) := by
  dsimp only [sourceSignedCorrection,sourceSignedFirst]
  split_ifs <;> simp

set_option pp.all true in
#check @sourceRx2
#print axioms sourceRx2
set_option pp.all true in
#check @original_rx2_words_are_exactly_twice_the_scalar_modulus
#print axioms original_rx2_words_are_exactly_twice_the_scalar_modulus
set_option pp.all true in
#check @sourceWideRadix
#print axioms sourceWideRadix
set_option pp.all true in
#check @sourceCorrectionShift
#print axioms sourceCorrectionShift
set_option pp.all true in
#check @original_correction_shift_is_between_half_and_whole_wide_radix
#print axioms original_correction_shift_is_between_half_and_whole_wide_radix
set_option pp.all true in
#check @sourceSignedFirst
#print axioms sourceSignedFirst
set_option pp.all true in
#check @sourceSignedCorrection
#print axioms sourceSignedCorrection
set_option pp.all true in
#check @original_two_signed_adjustments_derive_unsigned_wide_range
#print axioms original_two_signed_adjustments_derive_unsigned_wide_range
set_option pp.all true in
#check @original_correction_shift_has_zero_scalar_field_residue
#print axioms original_correction_shift_has_zero_scalar_field_residue
set_option pp.all true in
#check @original_two_signed_adjustments_retain_the_original_coefficient_field_residue
#print axioms original_two_signed_adjustments_retain_the_original_coefficient_field_residue
end ShielddSecurity.TransferBlstArmInverseSign01
