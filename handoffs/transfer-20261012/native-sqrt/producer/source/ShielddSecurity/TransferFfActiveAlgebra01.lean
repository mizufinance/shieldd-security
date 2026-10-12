import ShielddSecurity.TransferSqrtProducerField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfActiveAlgebra01
variable {F : Type} [Field F]
/-! Algebra of the actual ff active Tonelli-Shanks update. Least-k and root
order hypotheses are loop-state invariants, not desired return equations.
The source inner scan must derive the correction exponent separately. -/

theorem square_one_and_non_one_imply_minus_one (a : F) (square : a ^ 2 = 1) (nonOne : a ≠ 1) :
    a = -1 := by
  have factors : (a - 1) * (a + 1) = 0 := by
    calc
      _ = a ^ 2 - 1 := by ring
      _ = 0 := by rw [square]; ring
  rcases mul_eq_zero.mp factors with first | second
  · exact False.elim (nonOne (sub_eq_zero.mp first))
  · exact eq_neg_of_add_eq_zero_left second

theorem least_active_power_derives_negative_half_power (b : F) (k : Nat) (positive : 1 ≤ k)
    (power : b ^ (2 ^ k) = 1) (previous : b ^ (2 ^ (k - 1)) ≠ 1) :
    b ^ (2 ^ (k - 1)) = -1 := by
  apply square_one_and_non_one_imply_minus_one _ _ previous
  rw [← pow_mul]
  have count : k - 1 + 1 = k := by omega
  rw [← Nat.pow_succ, Nat.succ_eq_add_one, count]
  exact power

def correction (z : F) (v k : Nat) : F := z ^ (2 ^ (v - k - 1))

theorem active_correction_square_has_reduced_full_power (z : F) (v k : Nat) (smaller : k < v)
    (full : z ^ (2 ^ v) = 1) :
    (correction z v k ^ 2) ^ (2 ^ k) = 1 := by
  rw [correction, ← pow_mul, ← pow_mul]
  have count : v - k - 1 + 1 + k = v := by omega
  have exponent : 2 ^ (v - k - 1) * (2 * 2 ^ k) = 2 ^ v := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add, count]
  rw [exponent]
  exact full

theorem active_correction_square_has_reduced_negative_half_power
    (z : F) (v k : Nat) (positive : 1 ≤ k) (smaller : k < v)
    (half : z ^ (2 ^ (v - 1)) = -1) :
    (correction z v k ^ 2) ^ (2 ^ (k - 1)) = -1 := by
  rw [correction, ← pow_mul, ← pow_mul]
  have count : v - k - 1 + 1 + (k - 1) = v - 1 := by omega
  have exponent : 2 ^ (v - k - 1) * (2 * 2 ^ (k - 1)) = 2 ^ (v - 1) := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add, count]
  rw [exponent]
  exact half

theorem active_residue_update_derives_a_strictly_smaller_half_order_bound
    (b z : F) (v k : Nat) (positive : 1 ≤ k) (smaller : k < v)
    (power : b ^ (2 ^ k) = 1) (previous : b ^ (2 ^ (k - 1)) ≠ 1)
    (half : z ^ (2 ^ (v - 1)) = -1) :
    (b * correction z v k ^ 2) ^ (2 ^ (k - 1)) = 1 := by
  rw [mul_pow, least_active_power_derives_negative_half_power b k positive power previous,
    active_correction_square_has_reduced_negative_half_power z v k positive smaller half]
  ring

theorem active_candidate_update_preserves_exact_residue_tracking
    (input candidate b coefficient : F) (tracking : candidate ^ 2 = input * b) :
    (candidate * coefficient) ^ 2 = input * (b * coefficient ^ 2) := by
  calc
    _ = candidate ^ 2 * coefficient ^ 2 := by ring
    _ = (input * b) * coefficient ^ 2 := by rw [tracking]
    _ = _ := by ring

theorem active_unit_residue_finishes_the_actual_candidate
    (input candidate b : F) (tracking : candidate ^ 2 = input * b) (unit : b = 1) :
    candidate ^ 2 = input := by simpa only [unit, mul_one] using tracking

theorem active_k_one_update_finishes_the_actual_candidate
    (input candidate b z : F) (v : Nat) (larger : 1 < v)
    (tracking : candidate ^ 2 = input * b) (power : b ^ 2 = 1) (nonOne : b ≠ 1)
    (half : z ^ (2 ^ (v - 1)) = -1) :
    (candidate * correction z v 1) ^ 2 = input := by
  have updated := active_residue_update_derives_a_strictly_smaller_half_order_bound b z v 1
    (by decide) larger (by simpa only [pow_one] using power)
    (by simpa only [Nat.sub_self, pow_zero, pow_one] using nonOne) half
  have residue : b * correction z v 1 ^ 2 = 1 := by
    simpa only [Nat.sub_self, pow_zero, pow_one] using updated
  rw [active_candidate_update_preserves_exact_residue_tracking _ _ _ _ tracking, residue, mul_one]

theorem active_unit_residue_update_derives_the_finished_state
    (input candidate b z : F) (v : Nat) (larger : 1 < v)
    (tracking : candidate ^ 2 = input * b) (unit : b = 1)
    (half : z ^ (2 ^ (v - 1)) = -1) :
    candidate ^ 2 = input ∧
      (b * correction z v 1 ^ 2) ^ 2 = 1 ∧ (correction z v 1 ^ 2) ^ 2 = 1 := by
  have reduced := active_correction_square_has_reduced_negative_half_power z v 1 (by decide) larger half
  have negative : correction z v 1 ^ 2 = -1 := by
    simpa only [Nat.sub_self, pow_zero, pow_one] using reduced
  refine ⟨active_unit_residue_finishes_the_actual_candidate _ _ _ tracking unit,?_,?_⟩
  · rw [unit,one_mul,negative]
    ring
  · rw [negative]
    ring

set_option pp.all true in
#check @square_one_and_non_one_imply_minus_one
#print axioms square_one_and_non_one_imply_minus_one
set_option pp.all true in
#check @least_active_power_derives_negative_half_power
#print axioms least_active_power_derives_negative_half_power
set_option pp.all true in
#check @correction
#print axioms correction
set_option pp.all true in
#check @active_correction_square_has_reduced_full_power
#print axioms active_correction_square_has_reduced_full_power
set_option pp.all true in
#check @active_correction_square_has_reduced_negative_half_power
#print axioms active_correction_square_has_reduced_negative_half_power
set_option pp.all true in
#check @active_residue_update_derives_a_strictly_smaller_half_order_bound
#print axioms active_residue_update_derives_a_strictly_smaller_half_order_bound
set_option pp.all true in
#check @active_candidate_update_preserves_exact_residue_tracking
#print axioms active_candidate_update_preserves_exact_residue_tracking
set_option pp.all true in
#check @active_unit_residue_finishes_the_actual_candidate
#print axioms active_unit_residue_finishes_the_actual_candidate
set_option pp.all true in
#check @active_k_one_update_finishes_the_actual_candidate
#print axioms active_k_one_update_finishes_the_actual_candidate
set_option pp.all true in
#check @active_unit_residue_update_derives_the_finished_state
#print axioms active_unit_residue_update_derives_the_finished_state
end ShielddSecurity.TransferFfActiveAlgebra01
