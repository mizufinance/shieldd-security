import ShielddSecurity.TransferBlstArmInverseWordPackedWalk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordLoopCounter01
open TransferBlstArmInverseWordPackedStep01 (WordPackedState sourceWordPackedStep sourcePackedWordCode)
open TransferBlstArmInverseWordPackedWalk01 (sourceWordPackedWalk sourceWordPackedInitial)
open TransferBlstArmInversePackedWalk01 (sourcePackedWalk sourcePackedInitial)
attribute [local irreducible] sourceWordPackedStep sourceWordPackedWalk sourceWordPackedInitial
  sourcePackedWordCode sourcePackedWalk sourcePackedInitial

/-! Arithmetic source decrement/zero-test loop. A bounded unsigned counter
executes exactly its initial natural value of packed steps and reaches zero;
31 follows from the arbitrary-count theorem. This is a source branch model,
not a compiled PC/PSTATE/memory/ABI execution theorem. -/

def sourceCountedWordPackedRun : Nat → UInt64 × WordPackedState → UInt64 × WordPackedState
  | 0, state => state
  | fuel + 1, state =>
      if state.1 = 0 then state
      else sourceCountedWordPackedRun fuel (state.1 - 1, sourceWordPackedStep state.2)

theorem the_code_of_every_positive_bounded_source_counter_is_nonzero
    (count : Nat) (positive : 0 < count) (bounded : count < 18446744073709551616) :
    UInt64.ofNat count ≠ 0 := by
  have value : (UInt64.ofNat count).toNat = count := UInt64.toNat_ofNat_of_lt' bounded
  intro zero
  rw [zero, UInt64.toNat_zero] at value
  omega

theorem one_source_word_decrement_of_a_successor_counter_is_the_entire_predecessor_code
    (count : Nat) : UInt64.ofNat (count + 1) - 1 = UInt64.ofNat count := by
  rw [UInt64.ofNat_add]
  change (UInt64.ofNat count + 1) - 1 = UInt64.ofNat count
  exact UInt64.add_sub_cancel _ _

theorem every_sufficiently_fueled_bounded_word_counter_executes_exactly_its_entire_initial_count
    (count fuel : Nat) (words : WordPackedState) (enough : count ≤ fuel)
    (bounded : count < 18446744073709551616) :
    sourceCountedWordPackedRun fuel (UInt64.ofNat count, words) = (0, sourceWordPackedWalk count words) := by
  induction count generalizing fuel words with
  | zero =>
    cases fuel with
    | zero => simp [sourceCountedWordPackedRun, sourceWordPackedWalk]
    | succ fuel => simp [sourceCountedWordPackedRun, sourceWordPackedWalk]
  | succ count ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have nonzero := the_code_of_every_positive_bounded_source_counter_is_nonzero (count + 1) (Nat.succ_pos _) bounded
      have room : count ≤ fuel := by omega
      have smaller : count < 18446744073709551616 := by omega
      rw [sourceCountedWordPackedRun, if_neg nonzero,
        one_source_word_decrement_of_a_successor_counter_is_the_entire_predecessor_code, sourceWordPackedWalk]
      exact ih fuel (sourceWordPackedStep words) room smaller

attribute [local irreducible] sourceCountedWordPackedRun

theorem original31_source_counter_and_zero_test_derive_exactly31_entire_packed_word_steps
    (words : WordPackedState) :
    sourceCountedWordPackedRun 31 (31, words) = (0, sourceWordPackedWalk 31 words) := by
  exact every_sufficiently_fueled_bounded_word_counter_executes_exactly_its_entire_initial_count 31 31 words
    (Nat.le_refl _) (by decide)

theorem original31_counted_word_loop_with_original_constants_produces_the_entire_original_packed_state_code
    (a b : UInt64) : sourceCountedWordPackedRun 31 (31, sourceWordPackedInitial a b) =
      (0, sourcePackedWordCode (sourcePackedWalk 31 (sourcePackedInitial a.toNat b.toNat))) := by
  rw [original31_source_counter_and_zero_test_derive_exactly31_entire_packed_word_steps,
    TransferBlstArmInverseWordPackedWalk01.original31_step_source_uint64_word_loop_produces_the_entire_original_packed_state_code]

set_option pp.all true in
#check @sourceCountedWordPackedRun
#print axioms sourceCountedWordPackedRun
set_option pp.all true in
#check @the_code_of_every_positive_bounded_source_counter_is_nonzero
#print axioms the_code_of_every_positive_bounded_source_counter_is_nonzero
set_option pp.all true in
#check @one_source_word_decrement_of_a_successor_counter_is_the_entire_predecessor_code
#print axioms one_source_word_decrement_of_a_successor_counter_is_the_entire_predecessor_code
set_option pp.all true in
#check @every_sufficiently_fueled_bounded_word_counter_executes_exactly_its_entire_initial_count
#print axioms every_sufficiently_fueled_bounded_word_counter_executes_exactly_its_entire_initial_count
set_option pp.all true in
#check @original31_source_counter_and_zero_test_derive_exactly31_entire_packed_word_steps
#print axioms original31_source_counter_and_zero_test_derive_exactly31_entire_packed_word_steps
set_option pp.all true in
#check @original31_counted_word_loop_with_original_constants_produces_the_entire_original_packed_state_code
#print axioms original31_counted_word_loop_with_original_constants_produces_the_entire_original_packed_state_code
end ShielddSecurity.TransferBlstArmInverseWordLoopCounter01
