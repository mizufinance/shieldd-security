import ShielddSecurity.TransferScalarMontgomeryValue01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmCancellation01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarFourRoundWrapper01 (inverseWord modulusWords)

def sourceBlstR0 : UInt64 := 0xffff_fffe_ffff_ffff
def sourceBlstPLow : UInt64 := 0xffff_ffff_0000_0001
def sourceArmMultiplier (word : UInt64) : UInt64 := sourceBlstR0*word

theorem exact_locked_r0_and_modulus_low_limb_are_the_qualified_parameters :
    sourceBlstR0 = inverseWord ∧ sourceBlstPLow = modulusWords.headD 0 := by
  exact ⟨rfl,rfl⟩

theorem actual_arm_wrapped_multiplier_has_the_qualified_low_word_value (word : UInt64) :
    (sourceArmMultiplier word).toNat = (word*inverseWord).toNat := by
  rw [sourceArmMultiplier,exact_locked_r0_and_modulus_low_limb_are_the_qualified_parameters.1,
    UInt64.toNat_mul,UInt64.toNat_mul,Nat.mul_comm]

theorem actual_arm_low_word_sum_has_zero_remainder_from_the_locked_multiplier (word : UInt64) :
    (word.toNat+(sourceArmMultiplier word*sourceBlstPLow).toNat)%radix64 = 0 := by
  rw [UInt64.toNat_mul]
  change (word.toNat+(sourceArmMultiplier word).toNat*sourceBlstPLow.toNat % radix64)%radix64=0
  rw [Nat.add_mod_mod,
    actual_arm_wrapped_multiplier_has_the_qualified_low_word_value,
    exact_locked_r0_and_modulus_low_limb_are_the_qualified_parameters.2]
  exact TransferScalarMontgomeryValue01.wrapped_source_multiplier_cancels_any_low_word word

theorem actual_arm_skipped_low_addition_has_only_the_derived_zero_or_radix_sum (word : UInt64) :
    word.toNat+(sourceArmMultiplier word*sourceBlstPLow).toNat =
      if word=0 then 0 else radix64 := by
  have residue := actual_arm_low_word_sum_has_zero_remainder_from_the_locked_multiplier word
  have wordBound : word.toNat < radix64 := word.toNat_lt
  have productBound : (sourceArmMultiplier word*sourceBlstPLow).toNat < radix64 :=
    (sourceArmMultiplier word*sourceBlstPLow).toNat_lt
  by_cases zero : word=0
  · subst word
    rfl
  · have positive : 0 < word.toNat := by
      have numericNonzero : word.toNat ≠ 0 := fun numeric => zero (UInt64.toNat_inj.mp numeric)
      exact Nat.pos_of_ne_zero numericNonzero
    rw [if_neg zero]
    unfold radix64 at *
    omega

/-- Arithmetic flag predicate of locked ARM64 `subs xzr, low, #1`.
ISA register/flag execution and compiler/ABI correspondence remain separate. -/
def sourceArmSubsOneCarry (word : UInt64) : Bool := decide (1 ≤ word.toNat)

theorem actual_arm_subs_one_flag_predicate_is_the_derived_montgomery_low_add_carry
    (word : UInt64) :
    (sourceArmSubsOneCarry word).toNat =
      (word.toNat+(sourceArmMultiplier word*sourceBlstPLow).toNat)/radix64 := by
  rw [actual_arm_skipped_low_addition_has_only_the_derived_zero_or_radix_sum]
  by_cases zero : word=0
  · subst word
    simp [sourceArmSubsOneCarry]
  · have positive : 1 ≤ word.toNat := by
      have numericNonzero : word.toNat ≠ 0 := fun numeric => zero (UInt64.toNat_inj.mp numeric)
      exact Nat.one_le_iff_ne_zero.mpr numericNonzero
    simp [sourceArmSubsOneCarry,positive,zero,radix64]
set_option pp.all true in
#check @sourceBlstR0
#print axioms sourceBlstR0
set_option pp.all true in
#check @sourceBlstPLow
#print axioms sourceBlstPLow
set_option pp.all true in
#check @sourceArmMultiplier
#print axioms sourceArmMultiplier
set_option pp.all true in
#check @exact_locked_r0_and_modulus_low_limb_are_the_qualified_parameters
#print axioms exact_locked_r0_and_modulus_low_limb_are_the_qualified_parameters
set_option pp.all true in
#check @actual_arm_wrapped_multiplier_has_the_qualified_low_word_value
#print axioms actual_arm_wrapped_multiplier_has_the_qualified_low_word_value
set_option pp.all true in
#check @actual_arm_low_word_sum_has_zero_remainder_from_the_locked_multiplier
#print axioms actual_arm_low_word_sum_has_zero_remainder_from_the_locked_multiplier
set_option pp.all true in
#check @actual_arm_skipped_low_addition_has_only_the_derived_zero_or_radix_sum
#print axioms actual_arm_skipped_low_addition_has_only_the_derived_zero_or_radix_sum
set_option pp.all true in
#check @sourceArmSubsOneCarry
#print axioms sourceArmSubsOneCarry
set_option pp.all true in
#check @actual_arm_subs_one_flag_predicate_is_the_derived_montgomery_low_add_carry
#print axioms actual_arm_subs_one_flag_predicate_is_the_derived_montgomery_low_add_carry
end ShielddSecurity.TransferBlstArmCancellation01
