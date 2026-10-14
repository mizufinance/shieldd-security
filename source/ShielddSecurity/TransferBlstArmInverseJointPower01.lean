import ShielddSecurity.TransferBlstArmInverseWindowMagnitude01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseJointPower01

/-! UNRUN reusable joint-word and complete-prefix lower powers. The raw
nonzero joint CLZ interval supplies at least one high word's lower power;
an exact packed prefix then lifts that power into a complete input. Original
staged-prefix composition follows separately. Native execution stays open. -/

theorem original_uint64_joint_or_has_the_exact_natural_or_observation
    (a b : UInt64) : (a ||| b).toNat = a.toNat ||| b.toNat := by
  exact BitVec.toNat_or a.toBitVec b.toBitVec

theorem joint_word_lower_power_derives_a_lower_power_in_one_original_word
    (a b : UInt64) (power : Nat) (joint : 2 ^ power ≤ (a ||| b).toNat) :
    2 ^ power ≤ a.toNat ∨ 2 ^ power ≤ b.toNat := by
  by_cases left : 2 ^ power ≤ a.toNat
  · exact Or.inl left
  · right
    by_contra no
    have leftUpper : a.toNat < 2 ^ power := by omega
    have rightUpper : b.toNat < 2 ^ power := by omega
    have upper := Nat.or_lt_two_pow leftUpper rightUpper
    rw [original_uint64_joint_or_has_the_exact_natural_or_observation] at joint
    omega

theorem original_nonzero_joint_clz_derives_a_high_word_with_its_exact_lower_power
    (a b : UInt64) (nonzero : a ||| b ≠ 0) :
    let count := (a ||| b).toBitVec.clz.toNat
    2 ^ (63 - count) ≤ a.toNat ∨ 2 ^ (63 - count) ≤ b.toNat := by
  dsimp only
  have interval := TransferBlstArmInverseWindowMagnitude01.original_nonzero_joint_clz_derives_the_exact_raw_word_power_interval
    a b nonzero
  exact joint_word_lower_power_derives_a_lower_power_in_one_original_word _ _ _ interval.1

theorem exact_full_input_prefix_lifts_the_high_word_lower_power
    (input baseExponent highExponent high low tail : Nat)
    (wholePrefix : input = 2 ^ baseExponent * (2 ^ 64 * high + low) + tail)
    (highLower : 2 ^ highExponent ≤ high) :
    2 ^ (baseExponent + 64 + highExponent) ≤ input := by
  have highScaled := Nat.mul_le_mul_left (2 ^ 64) highLower
  have prefixScaled := Nat.mul_le_mul_left (2 ^ baseExponent) highScaled
  calc
    _ = 2 ^ baseExponent * (2 ^ 64 * 2 ^ highExponent) := by
      rw [Nat.pow_add (2 : Nat) (baseExponent + 64) highExponent,
        Nat.pow_add (2 : Nat) baseExponent 64, Nat.mul_assoc]
    _ ≤ 2 ^ baseExponent * (2 ^ 64 * high) := prefixScaled
    _ ≤ input := by
      rw [wholePrefix]
      exact Nat.le_trans
        (Nat.mul_le_mul_left _ (Nat.le_add_right (2 ^ 64 * high) low))
        (Nat.le_add_right _ tail)

set_option pp.all true in
#check @original_uint64_joint_or_has_the_exact_natural_or_observation
#print axioms original_uint64_joint_or_has_the_exact_natural_or_observation
set_option pp.all true in
#check @joint_word_lower_power_derives_a_lower_power_in_one_original_word
#print axioms joint_word_lower_power_derives_a_lower_power_in_one_original_word
set_option pp.all true in
#check @original_nonzero_joint_clz_derives_a_high_word_with_its_exact_lower_power
#print axioms original_nonzero_joint_clz_derives_a_high_word_with_its_exact_lower_power
set_option pp.all true in
#check @exact_full_input_prefix_lifts_the_high_word_lower_power
#print axioms exact_full_input_prefix_lifts_the_high_word_lower_power
end ShielddSecurity.TransferBlstArmInverseJointPower01
