import ShielddSecurity.TransferBlstArmInverseWordPackedStep01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordPackedWalk01
open TransferBlstArmInverseWordPackedStep01 (WordPackedState sourcePackedWordCode sourceWordPackedStep)
open TransferBlstArmInversePackedWalk01 (FactorWord sourcePackedInitial sourcePackedStep sourcePackedWalk)
open TransferBlstArmInversePackedFactorWords01 (sourcePackedRegisterWord)
attribute [local irreducible] sourcePackedWordCode sourceWordPackedStep sourcePackedStep sourcePackedWalk

/-! Symbolic source UInt64 packed loop. Exact source control and modular
register update correspondence composes by induction;31 is specialized only
after the arbitrary-count theorem. Actual counter/PSTATE instruction execution,
private callers, memory and ABI remain separate obligations. -/

def sourceWordPackedWalk : Nat → WordPackedState → WordPackedState
  | 0, words => words
  | count + 1, words => sourceWordPackedWalk count (sourceWordPackedStep words)

theorem every_symbolic_source_uint64_packed_walk_is_the_entire_code_of_the_original_packed_walk
    (count : Nat) (state : TransferBlstArmInversePackedWalk01.PackedState)
    (left : state.1 < 18446744073709551616) (right : state.2.1 < 18446744073709551616) :
    sourceWordPackedWalk count (sourcePackedWordCode state) = sourcePackedWordCode (sourcePackedWalk count state) := by
  induction count generalizing state with
  | zero => rw [sourceWordPackedWalk, sourcePackedWalk]
  | succ count ih =>
    have next := TransferBlstArmInverseWordPackedStep01.the_source_modulo64_packed_step_preserves_every_entire_natural_data_capacity
      state 18446744073709551616 left right
    rw [sourceWordPackedWalk,
      TransferBlstArmInverseWordPackedStep01.original_uint64_packed_word_step_is_the_entire_code_of_the_original_modulo64_packed_step state left right,
      ih (sourcePackedStep state) next.1 next.2, sourcePackedWalk]

def sourceWordPackedInitial (a b : UInt64) : WordPackedState :=
  (a, b, 9223372034707292160, 9223372039002259455)

theorem original_uint64_packed_initializer_is_the_entire_code_of_the_original_natural_packed_initializer
    (a b : UInt64) : sourceWordPackedInitial a b = sourcePackedWordCode (sourcePackedInitial a.toNat b.toNat) := by
  have first : sourcePackedRegisterWord (9223372034707292160 : FactorWord) = 9223372034707292160 := by
    unfold sourcePackedRegisterWord
    decide +kernel
  have last : sourcePackedRegisterWord (9223372039002259455 : FactorWord) = 9223372039002259455 := by
    unfold sourcePackedRegisterWord
    decide +kernel
  unfold sourceWordPackedInitial sourcePackedWordCode sourcePackedInitial
  simp only [UInt64.ofNat_toNat, first, last]

attribute [local irreducible] sourceWordPackedWalk sourceWordPackedInitial

theorem original31_step_source_uint64_word_loop_produces_the_entire_original_packed_state_code
    (a b : UInt64) :
    sourceWordPackedWalk 31 (sourceWordPackedInitial a b) =
      sourcePackedWordCode (sourcePackedWalk 31 (sourcePackedInitial a.toNat b.toNat)) := by
  rw [original_uint64_packed_initializer_is_the_entire_code_of_the_original_natural_packed_initializer]
  exact every_symbolic_source_uint64_packed_walk_is_the_entire_code_of_the_original_packed_walk 31
    (sourcePackedInitial a.toNat b.toNat) a.toNat_lt b.toNat_lt

set_option pp.all true in
#check @sourceWordPackedWalk
#print axioms sourceWordPackedWalk
set_option pp.all true in
#check @every_symbolic_source_uint64_packed_walk_is_the_entire_code_of_the_original_packed_walk
#print axioms every_symbolic_source_uint64_packed_walk_is_the_entire_code_of_the_original_packed_walk
set_option pp.all true in
#check @sourceWordPackedInitial
#print axioms sourceWordPackedInitial
set_option pp.all true in
#check @original_uint64_packed_initializer_is_the_entire_code_of_the_original_natural_packed_initializer
#print axioms original_uint64_packed_initializer_is_the_entire_code_of_the_original_natural_packed_initializer
set_option pp.all true in
#check @original31_step_source_uint64_word_loop_produces_the_entire_original_packed_state_code
#print axioms original31_step_source_uint64_word_loop_produces_the_entire_original_packed_state_code
end ShielddSecurity.TransferBlstArmInverseWordPackedWalk01
