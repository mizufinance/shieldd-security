import ShielddSecurity.TransferBlstArmInverseMismatchProgress01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseNaturalProgress01
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep sourceFactorWalk)

/-! Symbolic natural factor-walk progress. Each nonterminal step reduces the
exact pair bitlength by at least one. Every finite prefix either reaches a
zero first component or decreases by its length. Native execution is open. -/

theorem halving_a_positive_natural_value_decreases_its_exact_bitlength
    (value reduced : Nat) (positive : 0 < value) (bound : reduced ≤ value / 2) :
    sourceNatBitlength reduced + 1 ≤ sourceNatBitlength value := by
  have bitPositive : 1 ≤ sourceNatBitlength value := by
    simp only [sourceNatBitlength, if_neg (Nat.ne_of_gt positive)]
    omega
  have exponent : sourceNatBitlength value - 1 + 1 = sourceNatBitlength value := by omega
  have power : 2 ^ sourceNatBitlength value = 2 ^ (sourceNatBitlength value - 1) * 2 := by
    rw [←Nat.pow_succ, Nat.succ_eq_add_one, exponent]
  have upper := TransferBlstArmInverseBitlengthBudget01.every_natural_value_is_strictly_below_its_exact_bitlength_power value
  rw [power] at upper
  have halfUpper : value / 2 < 2 ^ (sourceNatBitlength value - 1) :=
    (Nat.div_lt_iff_lt_mul (by decide)).2 upper
  have reducedUpper := Nat.lt_of_le_of_lt bound halfUpper
  have bits := TransferBlstArmInverseBitlengthBudget01.a_strict_upper_power_bounds_the_exact_natural_bitlength _ _ reducedUpper
  omega

theorem every_nonterminal_original_natural_factor_step_decreases_pair_bitlength
    (s : SourceFactors) (positive : 0 < s.a) :
    sourceNatBitlength (sourceFactorStep s).a + sourceNatBitlength (sourceFactorStep s).b + 1 ≤
      sourceNatBitlength s.a + sourceNatBitlength s.b := by
  unfold sourceFactorStep
  by_cases even : s.a % 2 = 0
  · rw [if_pos even]
    have decrease := halving_a_positive_natural_value_decreases_its_exact_bitlength s.a (s.a / 2) positive (Nat.le_refl _)
    change sourceNatBitlength (s.a / 2) + sourceNatBitlength s.b + 1 ≤ _
    omega
  · rw [if_neg even]
    by_cases order : s.b ≤ s.a
    · rw [if_pos order]
      have decrease := halving_a_positive_natural_value_decreases_its_exact_bitlength s.a ((s.a - s.b) / 2) positive
        (Nat.div_le_div_right (Nat.sub_le _ _))
      change sourceNatBitlength ((s.a - s.b) / 2) + sourceNatBitlength s.b + 1 ≤ _
      omega
    · rw [if_neg order]
      have positiveB : 0 < s.b := by omega
      have decrease := halving_a_positive_natural_value_decreases_its_exact_bitlength s.b ((s.b - s.a) / 2) positiveB
        (Nat.div_le_div_right (Nat.sub_le _ _))
      change sourceNatBitlength ((s.b - s.a) / 2) + sourceNatBitlength s.a + 1 ≤ _
      omega

theorem a_zero_first_natural_component_stays_zero_for_every_factor_walk
    (count : Nat) (s : SourceFactors) (zero : s.a = 0) :
    (sourceFactorWalk count s).a = 0 := by
  induction count generalizing s with
  | zero => exact zero
  | succ count ih =>
    have next : (sourceFactorStep s).a = 0 := by simp only [sourceFactorStep, zero, Nat.zero_mod, if_true, Nat.zero_div]
    exact ih (sourceFactorStep s) next

theorem every_original_natural_factor_walk_reaches_zero_or_decreases_by_its_length
    (count : Nat) (s : SourceFactors) :
    (sourceFactorWalk count s).a = 0 ∨
      sourceNatBitlength (sourceFactorWalk count s).a + sourceNatBitlength (sourceFactorWalk count s).b + count ≤
        sourceNatBitlength s.a + sourceNatBitlength s.b := by
  induction count generalizing s with
  | zero => right; exact Nat.le_refl _
  | succ count ih =>
    by_cases zero : s.a = 0
    · left
      exact a_zero_first_natural_component_stays_zero_for_every_factor_walk _ s zero
    · rcases ih (sourceFactorStep s) with terminal | progress
      · left; exact terminal
      · right
        have one := every_nonterminal_original_natural_factor_step_decreases_pair_bitlength s (by omega)
        change sourceNatBitlength (sourceFactorWalk count (sourceFactorStep s)).a +
          sourceNatBitlength (sourceFactorWalk count (sourceFactorStep s)).b + (count + 1) ≤ _
        omega

set_option pp.all true in
#check @halving_a_positive_natural_value_decreases_its_exact_bitlength
#print axioms halving_a_positive_natural_value_decreases_its_exact_bitlength
set_option pp.all true in
#check @every_nonterminal_original_natural_factor_step_decreases_pair_bitlength
#print axioms every_nonterminal_original_natural_factor_step_decreases_pair_bitlength
set_option pp.all true in
#check @a_zero_first_natural_component_stays_zero_for_every_factor_walk
#print axioms a_zero_first_natural_component_stays_zero_for_every_factor_walk
set_option pp.all true in
#check @every_original_natural_factor_walk_reaches_zero_or_decreases_by_its_length
#print axioms every_original_natural_factor_walk_reaches_zero_or_decreases_by_its_length
end ShielddSecurity.TransferBlstArmInverseNaturalProgress01
