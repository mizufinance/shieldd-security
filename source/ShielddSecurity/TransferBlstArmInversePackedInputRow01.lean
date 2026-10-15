import ShielddSecurity.TransferBlstArmInversePackedFactorWords01
import ShielddSecurity.TransferBlstArmInverseOriginalRowWords01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePackedInputRow01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorWalk sourceFactorInitial)
open TransferBlstArmInversePackedWalk01 (sourcePackedWalk sourcePackedInitial)
open TransferBlstArmInversePackedFactorWords01 (sourcePackedFactorRegisterWords)
open TransferBlstArmInverseOriginalRowWords01 (sourceSelectFactorRow sourceOriginalFactorRow)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
attribute [local irreducible] sourceSignedWordCode sourceFactorWalk sourcePackedWalk sourcePackedFactorRegisterWords

/-! Original input windows, source packed recurrence and source UBFX/bias
decoding supply either complete factor-word row. Boolean selection is proved
over arbitrary coefficient integers first. Native control and ISA remain open. -/

def sourceSelectFactorWordRow (second : Bool) (words : UInt64 × UInt64 × UInt64 × UInt64) : UInt64 × UInt64 :=
  if second then (words.2.2.1, words.2.2.2) else (words.1, words.2.1)

def sourceFactorRowCodes (row : Int × Int) : UInt64 × UInt64 :=
  (sourceSignedWordCode row.1, sourceSignedWordCode row.2)

theorem encoding_four_coefficients_and_selecting_a_row_preserves_both_entire_integer_codes
    (second : Bool) (state : SourceFactors) :
    sourceSelectFactorWordRow second
      (sourceSignedWordCode state.f0, sourceSignedWordCode state.g0,
       sourceSignedWordCode state.f1, sourceSignedWordCode state.g1) =
      sourceFactorRowCodes (sourceSelectFactorRow second state.f0 state.g0 state.f1 state.g1) := by
  cases second <;> rfl

attribute [local irreducible] sourceSelectFactorWordRow sourceFactorRowCodes sourceSelectFactorRow sourceOriginalFactorRow

def sourceInputPackedFactorRegisters (a b : SourceFourWords) : UInt64 × UInt64 × UInt64 × UInt64 :=
  sourcePackedFactorRegisterWords (sourcePackedWalk 31 (sourcePackedInitial
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)))

def sourceOriginalInputFactorWords (second : Bool) (a b : SourceFourWords) : UInt64 × UInt64 :=
  sourceSelectFactorWordRow second (sourceInputPackedFactorRegisters a b)

theorem original_input_window_packed_registers_and_slot_decoders_produce_both_entire_factor_row_codes
    (second : Bool) (a b : SourceFourWords) :
    sourceOriginalInputFactorWords second a b = sourceFactorRowCodes (sourceOriginalFactorRow 31 second a b) := by
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  have entire := TransferBlstArmInversePackedFactorWords01.original_modulo64_packed_walk_and_ubfx_bias_subtraction_derive_all_four_entire_factor_codes approxA approxB
  unfold sourceOriginalInputFactorWords sourceInputPackedFactorRegisters
  rw [entire]
  unfold sourceOriginalFactorRow
  exact encoding_four_coefficients_and_selecting_a_row_preserves_both_entire_integer_codes
    second (sourceFactorWalk 31 (sourceFactorInitial approxA approxB))

set_option pp.all true in
#check @sourceSelectFactorWordRow
#print axioms sourceSelectFactorWordRow
set_option pp.all true in
#check @sourceFactorRowCodes
#print axioms sourceFactorRowCodes
set_option pp.all true in
#check @encoding_four_coefficients_and_selecting_a_row_preserves_both_entire_integer_codes
#print axioms encoding_four_coefficients_and_selecting_a_row_preserves_both_entire_integer_codes
set_option pp.all true in
#check @sourceInputPackedFactorRegisters
#print axioms sourceInputPackedFactorRegisters
set_option pp.all true in
#check @sourceOriginalInputFactorWords
#print axioms sourceOriginalInputFactorWords
set_option pp.all true in
#check @original_input_window_packed_registers_and_slot_decoders_produce_both_entire_factor_row_codes
#print axioms original_input_window_packed_registers_and_slot_decoders_produce_both_entire_factor_row_codes
end ShielddSecurity.TransferBlstArmInversePackedInputRow01
