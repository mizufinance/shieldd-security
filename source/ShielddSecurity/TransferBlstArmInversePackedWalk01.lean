import ShielddSecurity.TransferBlstArmInversePack01
import ShielddSecurity.TransferBlstArmInverseSharp01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePackedWalk01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)
open TransferBlstArmInversePack01
  (sourceBiasedPair sourceBiasPair sourceDecodeLow sourceDecodeHigh)

attribute [local irreducible] sourceFactorWalk

/-! Modulo64 arithmetic interpretation of the two packed factor registers.
The exact parity/borrow control updates and biased subtract/double recurrences
are composed symbolically. Final decoded coefficients follow from initialized
31-step slot bounds. Actual control-register/bit-operation/ISA correspondence,
approximate batch progress, full coefficient production and native execution
remain separate; this is a source arithmetic model, not native execution. -/

abbrev FactorWord := ZMod 18446744073709551616
abbrev PackedState := Nat × Nat × FactorWord × FactorWord

local instance factorWordNonzero : NeZero (18446744073709551616:Nat) := ⟨by decide⟩

def sourceFactorEncoding (s : SourceFactors) : PackedState :=
  (s.a,s.b,(sourceBiasedPair s.f0 s.g0:FactorWord),(sourceBiasedPair s.f1 s.g1:FactorWord))

def sourcePackedInitial (a b : Nat) : PackedState :=
  (a,b,9223372034707292160,9223372039002259455)

def sourcePackedStep (s : PackedState) : PackedState :=
  if s.1%2=0 then (s.1/2,s.2.1,s.2.2.1,2*s.2.2.2-(sourceBiasPair:FactorWord))
  else if s.2.1≤s.1 then
    ((s.1-s.2.1)/2,s.2.1,s.2.2.1-s.2.2.2+(sourceBiasPair:FactorWord),
      2*s.2.2.2-(sourceBiasPair:FactorWord))
  else ((s.2.1-s.1)/2,s.1,s.2.2.2-s.2.2.1+(sourceBiasPair:FactorWord),
      2*s.2.2.1-(sourceBiasPair:FactorWord))

theorem original_packed_constants_are_the_encoded_factor_initialization (a b : Nat) :
    sourcePackedInitial a b=sourceFactorEncoding (sourceFactorInitial a b) := by
  have constants := TransferBlstArmInversePack01.original_packed_factor_initialization_is_the_biased_identity_matrix
  unfold sourcePackedInitial sourceFactorEncoding sourceFactorInitial
  change (a,b,(9223372034707292160:FactorWord),(9223372039002259455:FactorWord))=
    (a,b,(sourceBiasedPair 1 0:FactorWord),(sourceBiasedPair 0 1:FactorWord))
  rw [constants.1,constants.2.1]
  norm_cast

theorem original_modulo64_packed_subtract_and_bias_encodes_row_subtraction
    (f g h k : Int) :
    (sourceBiasedPair f g:FactorWord)-(sourceBiasedPair h k:FactorWord)+(sourceBiasPair:FactorWord)=
      (sourceBiasedPair (f-h) (g-k):FactorWord) := by
  have identity := congrArg (fun value : Int => (value:FactorWord))
    (TransferBlstArmInversePack01.original_packed_subtract_and_bias_derives_row_subtraction f g h k)
  simpa only [Int.cast_add,Int.cast_sub] using identity

theorem original_modulo64_packed_double_and_bias_encodes_row_doubling (f g : Int) :
    2*(sourceBiasedPair f g:FactorWord)-(sourceBiasPair:FactorWord)=
      (sourceBiasedPair (2*f) (2*g):FactorWord) := by
  have identity := congrArg (fun value : Int => (value:FactorWord))
    (TransferBlstArmInversePack01.original_packed_double_and_bias_derives_row_doubling f g)
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat] using identity

theorem original_packed_register_step_is_the_encoded_integer_factor_step (s : SourceFactors) :
    sourcePackedStep (sourceFactorEncoding s)=sourceFactorEncoding (sourceFactorStep s) := by
  by_cases even : s.a%2=0
  · simp only [sourcePackedStep,sourceFactorEncoding,sourceFactorStep,if_pos even]
    rw [original_modulo64_packed_double_and_bias_encodes_row_doubling]
  · by_cases ordered : s.b≤s.a
    · simp only [sourcePackedStep,sourceFactorEncoding,sourceFactorStep,if_neg even,if_pos ordered]
      rw [original_modulo64_packed_subtract_and_bias_encodes_row_subtraction,
        original_modulo64_packed_double_and_bias_encodes_row_doubling]
    · simp only [sourcePackedStep,sourceFactorEncoding,sourceFactorStep,if_neg even,if_neg ordered]
      rw [original_modulo64_packed_subtract_and_bias_encodes_row_subtraction,
        original_modulo64_packed_double_and_bias_encodes_row_doubling]

def sourcePackedWalk : Nat → PackedState → PackedState
  | 0,s => s
  | count+1,s => sourcePackedWalk count (sourcePackedStep s)

attribute [local irreducible] sourcePackedWalk

theorem symbolic_original_packed_register_walk_is_the_encoded_integer_factor_walk
    (count : Nat) (s : SourceFactors) :
    sourcePackedWalk count (sourceFactorEncoding s)=sourceFactorEncoding (sourceFactorWalk count s) := by
  induction count generalizing s with
  | zero => simp only [sourcePackedWalk,sourceFactorWalk]
  | succ count ih =>
      rw [sourcePackedWalk,original_packed_register_step_is_the_encoded_integer_factor_step,ih,sourceFactorWalk]

theorem original_bounded_factor_word_recovers_the_complete_integer_biased_pair
    (f g : Int) (lowNonnegative : 0≤f+2147483647) (lowBounded : f+2147483647<4294967296)
    (highNonnegative : 0≤g+2147483647) (highBounded : g+2147483647<4294967296) :
    (((sourceBiasedPair f g:FactorWord).val:Nat):Int)=sourceBiasedPair f g := by
  have range := TransferBlstArmInversePack01.bounded_original_biased_slots_derive_the_full_unsigned_word_range
    f g lowNonnegative lowBounded highNonnegative highBounded
  rw [ZMod.val_intCast]
  simpa only [Nat.cast_ofNat] using (Int.emod_eq_of_lt range.1 range.2)

theorem original_initialized_31_packed_walk_decodes_all_four_actual_factor_coefficients (a b : Nat) :
    let integer := sourceFactorWalk 31 (sourceFactorInitial a b);
    let packed := sourcePackedWalk 31 (sourcePackedInitial a b);
    sourceDecodeLow (packed.2.2.1.val:Int)=integer.f0 ∧
      sourceDecodeHigh (packed.2.2.1.val:Int)=integer.g0 ∧
      sourceDecodeLow (packed.2.2.2.val:Int)=integer.f1 ∧
      sourceDecodeHigh (packed.2.2.2.val:Int)=integer.g1 := by
  dsimp only
  rw [original_packed_constants_are_the_encoded_factor_initialization,
    symbolic_original_packed_register_walk_is_the_encoded_integer_factor_walk]
  let integer := sourceFactorWalk 31 (sourceFactorInitial a b)
  have bounds := TransferBlstArmInverseSharp01.every_original_31_step_factor_coefficient_fits_its_biased_unsigned_slot
    31 a b (by decide) (by decide)
  change 0≤ integer.f0+2147483647 ∧ integer.f0+2147483647<4294967296 ∧
    0≤ integer.g0+2147483647 ∧ integer.g0+2147483647<4294967296 ∧
    0≤ integer.f1+2147483647 ∧ integer.f1+2147483647<4294967296 ∧
    0≤ integer.g1+2147483647 ∧ integer.g1+2147483647<4294967296 at bounds
  rcases bounds with ⟨lf,uf,lg,ug,lh,uh,lk,uk⟩
  change sourceDecodeLow ((sourceBiasedPair integer.f0 integer.g0:FactorWord).val:Int)=integer.f0 ∧
    sourceDecodeHigh ((sourceBiasedPair integer.f0 integer.g0:FactorWord).val:Int)=integer.g0 ∧
    sourceDecodeLow ((sourceBiasedPair integer.f1 integer.g1:FactorWord).val:Int)=integer.f1 ∧
    sourceDecodeHigh ((sourceBiasedPair integer.f1 integer.g1:FactorWord).val:Int)=integer.g1
  rw [original_bounded_factor_word_recovers_the_complete_integer_biased_pair _ _ lf uf lg ug,
    original_bounded_factor_word_recovers_the_complete_integer_biased_pair _ _ lh uh lk uk]
  have first := TransferBlstArmInversePack01.original_biased_slot_extraction_and_bias_removal_recovers_both_coefficients
    integer.f0 integer.g0 lf uf
  have second := TransferBlstArmInversePack01.original_biased_slot_extraction_and_bias_removal_recovers_both_coefficients
    integer.f1 integer.g1 lh uh
  exact ⟨first.1,first.2,second.1,second.2⟩

set_option pp.all true in
#check @FactorWord
#print axioms FactorWord
set_option pp.all true in
#check @PackedState
#print axioms PackedState
set_option pp.all true in
#check @factorWordNonzero
#print axioms factorWordNonzero
set_option pp.all true in
#check @sourceFactorEncoding
#print axioms sourceFactorEncoding
set_option pp.all true in
#check @sourcePackedInitial
#print axioms sourcePackedInitial
set_option pp.all true in
#check @sourcePackedStep
#print axioms sourcePackedStep
set_option pp.all true in
#check @original_packed_constants_are_the_encoded_factor_initialization
#print axioms original_packed_constants_are_the_encoded_factor_initialization
set_option pp.all true in
#check @original_modulo64_packed_subtract_and_bias_encodes_row_subtraction
#print axioms original_modulo64_packed_subtract_and_bias_encodes_row_subtraction
set_option pp.all true in
#check @original_modulo64_packed_double_and_bias_encodes_row_doubling
#print axioms original_modulo64_packed_double_and_bias_encodes_row_doubling
set_option pp.all true in
#check @original_packed_register_step_is_the_encoded_integer_factor_step
#print axioms original_packed_register_step_is_the_encoded_integer_factor_step
set_option pp.all true in
#check @sourcePackedWalk
#print axioms sourcePackedWalk
set_option pp.all true in
#check @symbolic_original_packed_register_walk_is_the_encoded_integer_factor_walk
#print axioms symbolic_original_packed_register_walk_is_the_encoded_integer_factor_walk
set_option pp.all true in
#check @original_bounded_factor_word_recovers_the_complete_integer_biased_pair
#print axioms original_bounded_factor_word_recovers_the_complete_integer_biased_pair
set_option pp.all true in
#check @original_initialized_31_packed_walk_decodes_all_four_actual_factor_coefficients
#print axioms original_initialized_31_packed_walk_decodes_all_four_actual_factor_coefficients
end ShielddSecurity.TransferBlstArmInversePackedWalk01
