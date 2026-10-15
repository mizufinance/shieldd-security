import ShielddSecurity.TransferBlstArmInverseWordPairControl01
import ShielddSecurity.TransferBlstArmInverseWordPackedArithmetic01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordPackedStep01
open TransferBlstArmInversePackedWalk01 (FactorWord PackedState sourcePackedStep)
open TransferBlstArmInversePack01 (sourceBiasPair)
open TransferBlstArmInversePackedFactorWords01 (sourcePackedRegisterWord)
open TransferBlstArmInverseWordPairControl01 (sourceNaturalPairControlStep sourceWordPairControlStep)
open TransferBlstArmInverseWordParityMask01 (sourceParityWordMask)
open TransferBlstArmInverseWordPackedArithmetic01
attribute [local irreducible] sourceParityWordMask sourceWordPairControlStep sourcePackedRegisterWord

/-! A complete source UInt64 packed loop step, including parity mask,
no-borrow selects and biased word updates, is the exact code of the
existing natural/modulo64 packed step. Natural input capacity is explicit;
PSTATE, memory/ABI and compiled instruction execution remain separate. -/

abbrev WordPackedState := UInt64 × UInt64 × UInt64 × UInt64

def sourcePackedWordCode (state : PackedState) : WordPackedState :=
  (UInt64.ofNat state.1, UInt64.ofNat state.2.1,
   sourcePackedRegisterWord state.2.2.1, sourcePackedRegisterWord state.2.2.2)

def sourceWordPackedStep (words : WordPackedState) : WordPackedState :=
  let mask := sourceParityWordMask words.1
  let noBorrow := decide ((words.2.1 &&& mask).toNat ≤ words.1.toNat)
  let left := if noBorrow then words.2.2.1 else words.2.2.2
  let right := if noBorrow then words.2.2.2 else words.2.2.1
  let data := sourceWordPairControlStep words.1 words.2.1
  (data.1, data.2, left - (right &&& mask) + ((9223372034707292159 : UInt64) &&& mask),
   right + right - 9223372034707292159)

theorem the_entire_source_word_pair_step_is_the_exact_code_of_its_natural_data_step
    (a b : UInt64) : sourceWordPairControlStep a b =
      (UInt64.ofNat (sourceNaturalPairControlStep a.toNat b.toNat).1,
       UInt64.ofNat (sourceNaturalPairControlStep a.toNat b.toNat).2) := by
  have data := TransferBlstArmInverseWordPairControl01.original_word_mask_subtract_borrow_select_and_shift_derive_the_entire_natural_pair_step a b
  apply Prod.ext
  · have first := congrArg Prod.fst data
    have encoded := congrArg UInt64.ofNat first
    simpa only [UInt64.ofNat_toNat] using encoded
  · have last := congrArg Prod.snd data
    have encoded := congrArg UInt64.ofNat last
    simpa only [UInt64.ofNat_toNat] using encoded

theorem source_natural_pair_data_is_the_entire_data_part_of_the_modulo64_packed_step
    (state : PackedState) : sourceNaturalPairControlStep state.1 state.2.1 =
      ((sourcePackedStep state).1, (sourcePackedStep state).2.1) := by
  by_cases even : state.1 % 2 = 0
  · simp only [sourceNaturalPairControlStep, sourcePackedStep, if_pos even]
  · by_cases ordered : state.2.1 ≤ state.1
    · simp only [sourceNaturalPairControlStep, sourcePackedStep, if_neg even, if_pos ordered]
    · simp only [sourceNaturalPairControlStep, sourcePackedStep, if_neg even, if_neg ordered]

theorem the_source_modulo64_packed_step_preserves_every_entire_natural_data_capacity
    (state : PackedState) (capacity : Nat) (left : state.1 < capacity) (right : state.2.1 < capacity) :
    (sourcePackedStep state).1 < capacity ∧ (sourcePackedStep state).2.1 < capacity := by
  have bounded := TransferBlstArmInverseWordPairControl01.every_natural_pair_control_step_never_increases_the_entire_input_maximum state.1 state.2.1
  rw [source_natural_pair_data_is_the_entire_data_part_of_the_modulo64_packed_step] at bounded
  have maximum : max state.1 state.2.1 < capacity := Nat.max_lt.mpr ⟨left, right⟩
  exact ⟨Nat.lt_of_le_of_lt bounded.1 maximum, Nat.lt_of_le_of_lt bounded.2 maximum⟩

theorem original_uint64_packed_word_step_is_the_entire_code_of_the_original_modulo64_packed_step
    (state : PackedState) (leftBound : state.1 < 18446744073709551616)
    (rightBound : state.2.1 < 18446744073709551616) :
    sourceWordPackedStep (sourcePackedWordCode state) = sourcePackedWordCode (sourcePackedStep state) := by
  rcases state with ⟨a, b, f, g⟩
  have aValue : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' leftBound
  have bValue : (UInt64.ofNat b).toNat = b := UInt64.toNat_ofNat_of_lt' rightBound
  have data := the_entire_source_word_pair_step_is_the_exact_code_of_its_natural_data_step (UInt64.ofNat a) (UInt64.ofNat b)
  rw [aValue, bValue] at data
  have parityBound := Nat.mod_lt a (by decide : 0 < 2)
  have bias := original_biased_pair_constant_has_the_exact_entire_uint64_word_code
  by_cases even : a % 2 = 0
  · have notOdd : ¬a % 2 = 1 := by omega
    have mask : sourceParityWordMask (UInt64.ofNat a) = 0 := by
      simp only [TransferBlstArmInverseWordParityMask01.original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask,
        aValue, if_neg notOdd]
    simp only [sourceWordPackedStep, sourcePackedWordCode, mask, UInt64.and_zero, UInt64.toNat_zero,
      Nat.zero_le, decide_true, ite_true, UInt64.sub_zero, UInt64.add_zero,
      data, sourceNaturalPairControlStep, sourcePackedStep, if_pos even]
    simp only [two_mul, entire_modulo64_packed_register_subtraction_is_exact_uint64_word_subtraction,
      entire_modulo64_packed_register_addition_is_exact_uint64_word_addition, bias]
  · have odd : a % 2 = 1 := by omega
    have mask : sourceParityWordMask (UInt64.ofNat a) = -1 := by
      simp only [TransferBlstArmInverseWordParityMask01.original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask,
        aValue, if_pos odd]
    by_cases ordered : b ≤ a
    · have noBorrow : decide ((UInt64.ofNat b).toNat ≤ (UInt64.ofNat a).toNat) = true := by
        rw [aValue, bValue]
        exact decide_eq_true ordered
      simp only [sourceWordPackedStep, sourcePackedWordCode, mask, UInt64.and_neg_one, noBorrow,
        ite_true, data, sourceNaturalPairControlStep, sourcePackedStep, if_neg even, if_pos ordered]
      simp only [two_mul, entire_modulo64_packed_register_addition_is_exact_uint64_word_addition,
        entire_modulo64_packed_register_subtraction_is_exact_uint64_word_subtraction, bias]
    · have noBorrow : decide ((UInt64.ofNat b).toNat ≤ (UInt64.ofNat a).toNat) = false := by
        rw [aValue, bValue]
        exact decide_eq_false ordered
      simp only [sourceWordPackedStep, sourcePackedWordCode, mask, UInt64.and_neg_one, noBorrow,
        Bool.false_eq_true, ite_false, data, sourceNaturalPairControlStep, sourcePackedStep, if_neg even, if_neg ordered]
      simp only [two_mul, entire_modulo64_packed_register_addition_is_exact_uint64_word_addition,
        entire_modulo64_packed_register_subtraction_is_exact_uint64_word_subtraction, bias]

set_option pp.all true in
#check @WordPackedState
#print axioms WordPackedState
set_option pp.all true in
#check @sourcePackedWordCode
#print axioms sourcePackedWordCode
set_option pp.all true in
#check @sourceWordPackedStep
#print axioms sourceWordPackedStep
set_option pp.all true in
#check @the_entire_source_word_pair_step_is_the_exact_code_of_its_natural_data_step
#print axioms the_entire_source_word_pair_step_is_the_exact_code_of_its_natural_data_step
set_option pp.all true in
#check @source_natural_pair_data_is_the_entire_data_part_of_the_modulo64_packed_step
#print axioms source_natural_pair_data_is_the_entire_data_part_of_the_modulo64_packed_step
set_option pp.all true in
#check @the_source_modulo64_packed_step_preserves_every_entire_natural_data_capacity
#print axioms the_source_modulo64_packed_step_preserves_every_entire_natural_data_capacity
set_option pp.all true in
#check @original_uint64_packed_word_step_is_the_entire_code_of_the_original_modulo64_packed_step
#print axioms original_uint64_packed_word_step_is_the_entire_code_of_the_original_modulo64_packed_step
end ShielddSecurity.TransferBlstArmInverseWordPackedStep01
