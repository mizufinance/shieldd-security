import ShielddSecurity.TransferScalarInverseCorrectness01
import ShielddSecurity.TransferScalarPowBitInteger01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPowField01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarPowInvariant01
open TransferScalarFieldValues01
/-! Symbolic source bit/word folds connect the actual modeled canonical
square/multiply operations and exact reconstructed word exponent with the
mathematical field power. Source ONE supplies the initial invariant; final
endpoints have no caller desired-value premise. Native Choice/compiler/caller
binding remains separate. -/

theorem source_constant_time_bit_step_derives_exact_field_exponent
    (self current : CanonicalScalar) (exponent : Nat) (bit : Bool)
    (currentValue : montgomeryValue current.words = montgomeryValue self.words ^ exponent % nullifierModulus) :
    montgomeryValue (sourceConstantTimeStep self current bit).words =
      montgomeryValue self.words ^ (exponent * 2 + (if bit then 1 else 0)) % nullifierModulus := by
  cases bit with
  | false =>
    change montgomeryValue (sourceCanonicalSquare current).words =
      montgomeryValue self.words ^ (exponent * 2 + 0) % nullifierModulus
    rw [actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value, currentValue]
    simp only [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_mod, Nat.add_zero]
    rw [Nat.pow_mul, Nat.pow_two]
  | true =>
    change montgomeryValue (sourceCanonicalMul (sourceCanonicalSquare current) self).words =
      montgomeryValue self.words ^ (exponent * 2 + 1) % nullifierModulus
    rw [actual_modeled_canonical_multiply_has_exact_mathematical_field_value,
      actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value, currentValue]
    simp only [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_mod]
    rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]

theorem source_variable_time_bit_step_derives_exact_field_exponent
    (self current : CanonicalScalar) (exponent : Nat) (bit : Bool)
    (currentValue : montgomeryValue current.words = montgomeryValue self.words ^ exponent % nullifierModulus) :
    montgomeryValue (sourceVariableTimeStep self current bit).words =
      montgomeryValue self.words ^ (exponent * 2 + (if bit then 1 else 0)) % nullifierModulus := by
  rw [← source_constant_and_variable_bit_steps_return_identical_fields]
  exact source_constant_time_bit_step_derives_exact_field_exponent self current exponent bit currentValue

theorem symbolic_source_bit_power_fold_derives_exact_field_exponent
    (self current : CanonicalScalar) (word : UInt64) (indices : List Nat) (exponent : Nat)
    (currentValue : montgomeryValue current.words = montgomeryValue self.words ^ exponent % nullifierModulus) :
    montgomeryValue (indices.foldl (fun result index => sourceConstantTimeStep self result (sourcePowBit word index)) current).words =
      montgomeryValue self.words ^ (indices.foldl
        (fun value index => value * 2 + (if sourcePowBit word index then 1 else 0)) exponent) % nullifierModulus := by
  induction indices generalizing current exponent with
  | nil => exact currentValue
  | cons index rest ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (source_constant_time_bit_step_derives_exact_field_exponent self current exponent (sourcePowBit word index) currentValue)

theorem symbolic_source_word_power_fold_derives_exact_field_exponent
    (self current : CanonicalScalar) (words : List UInt64) (exponent : Nat)
    (currentValue : montgomeryValue current.words = montgomeryValue self.words ^ exponent % nullifierModulus) :
    montgomeryValue (words.foldl (fun result word => (List.range 64).reverse.foldl
      (fun next index => sourceConstantTimeStep self next (sourcePowBit word index)) result) current).words =
      montgomeryValue self.words ^ (words.foldl (fun value word => (List.range 64).reverse.foldl
        (fun next index => next * 2 + (if sourcePowBit word index then 1 else 0)) value) exponent) % nullifierModulus := by
  induction words generalizing current exponent with
  | nil => exact currentValue
  | cons word rest ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (symbolic_source_bit_power_fold_derives_exact_field_exponent self current word (List.range 64).reverse exponent currentValue)

theorem exact_source_constant_time_pow_has_mathematical_little_endian_field_power
    (self : CanonicalScalar) (exponent : Vector UInt64 4) :
    montgomeryValue (sourcePow self exponent).words =
      montgomeryValue self.words ^ packWords exponent.toList % nullifierModulus := by
  have initial : montgomeryValue sourceOne.words = montgomeryValue self.words ^ 0 % nullifierModulus := by
    rw [source_zero_and_one_constants_have_exact_canonical_montgomery_keys.2, Nat.pow_zero,
      Nat.mod_eq_of_lt (by decide : 1 < nullifierModulus)]
  have walked := symbolic_source_word_power_fold_derives_exact_field_exponent self sourceOne exponent.toList.reverse 0 initial
  change montgomeryValue (sourcePow self exponent).words = _ at walked
  rw [TransferScalarPowBitInteger01.symbolic_source_reversed_word_bit_walk_reconstructs_exact_little_endian_integer,
    Nat.zero_mul, Nat.zero_add] at walked
  exact walked

theorem exact_source_variable_time_pow_has_mathematical_little_endian_field_power
    (self : CanonicalScalar) (exponent : Vector UInt64 4) :
    montgomeryValue (sourcePowVartime self exponent).words =
      montgomeryValue self.words ^ packWords exponent.toList % nullifierModulus := by
  rw [← source_constant_and_variable_pow_loops_return_identical_fields]
  exact exact_source_constant_time_pow_has_mathematical_little_endian_field_power self exponent

set_option pp.all true in
#check @source_constant_time_bit_step_derives_exact_field_exponent
#print axioms source_constant_time_bit_step_derives_exact_field_exponent
set_option pp.all true in
#check @source_variable_time_bit_step_derives_exact_field_exponent
#print axioms source_variable_time_bit_step_derives_exact_field_exponent
set_option pp.all true in
#check @symbolic_source_bit_power_fold_derives_exact_field_exponent
#print axioms symbolic_source_bit_power_fold_derives_exact_field_exponent
set_option pp.all true in
#check @symbolic_source_word_power_fold_derives_exact_field_exponent
#print axioms symbolic_source_word_power_fold_derives_exact_field_exponent
set_option pp.all true in
#check @exact_source_constant_time_pow_has_mathematical_little_endian_field_power
#print axioms exact_source_constant_time_pow_has_mathematical_little_endian_field_power
set_option pp.all true in
#check @exact_source_variable_time_pow_has_mathematical_little_endian_field_power
#print axioms exact_source_variable_time_pow_has_mathematical_little_endian_field_power
end ShielddSecurity.TransferScalarPowField01
