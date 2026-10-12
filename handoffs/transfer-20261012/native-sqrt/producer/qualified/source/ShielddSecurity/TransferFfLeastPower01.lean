import ShielddSecurity.TransferFfActiveAlgebra01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfLeastPower01
variable {F : Type} [Field F] [DecidableEq F]
/-! The active state order bound derives existence and minimality of a
positive search index. Native inner-scan correspondence must identify this
derived index; it is not accepted as a chosen output or caller success. -/

omit [DecidableEq F] in
theorem active_half_order_bound_derives_a_positive_search_witness
    (b : F) (v : Nat) (active : 1 < v) (bound : b ^ (2 ^ (v - 1)) = 1) :
    ∃ k : Nat, 1 ≤ k ∧ k < v ∧ b ^ (2 ^ k) = 1 := by
  exact ⟨v - 1, by omega, by omega, bound⟩

def leastPositiveExponent (b : F) (v : Nat) (active : 1 < v)
    (bound : b ^ (2 ^ (v - 1)) = 1) : Nat :=
  Nat.find (active_half_order_bound_derives_a_positive_search_witness b v active bound)

theorem derived_least_positive_exponent_has_exact_search_bounds_and_power
    (b : F) (v : Nat) (active : 1 < v) (bound : b ^ (2 ^ (v - 1)) = 1) :
    1 ≤ leastPositiveExponent b v active bound ∧
      leastPositiveExponent b v active bound < v ∧
      b ^ (2 ^ leastPositiveExponent b v active bound) = 1 :=
  Nat.find_spec (active_half_order_bound_derives_a_positive_search_witness b v active bound)

theorem every_earlier_positive_power_before_the_derived_index_is_not_one
    (b : F) (v : Nat) (active : 1 < v) (bound : b ^ (2 ^ (v - 1)) = 1)
    (j : Nat) (positive : 1 ≤ j) (earlier : j < leastPositiveExponent b v active bound) :
    b ^ (2 ^ j) ≠ 1 := by
  intro one
  have indexBound := (derived_least_positive_exponent_has_exact_search_bounds_and_power b v active bound).2.1
  exact Nat.find_min (active_half_order_bound_derives_a_positive_search_witness b v active bound) earlier
    ⟨positive, by omega, one⟩

theorem nonunit_active_residue_has_a_negative_half_power_at_its_derived_index
    (b : F) (v : Nat) (active : 1 < v) (bound : b ^ (2 ^ (v - 1)) = 1) (nonunit : b ≠ 1) :
    b ^ (2 ^ (leastPositiveExponent b v active bound - 1)) = -1 := by
  have spec := derived_least_positive_exponent_has_exact_search_bounds_and_power b v active bound
  apply TransferFfActiveAlgebra01.least_active_power_derives_negative_half_power _ _ spec.1 spec.2.2
  by_cases first : leastPositiveExponent b v active bound = 1
  · simpa only [first, Nat.sub_self, pow_zero, pow_one] using nonunit
  · apply every_earlier_positive_power_before_the_derived_index_is_not_one b v active bound
    · omega
    · omega

set_option pp.all true in
#check @active_half_order_bound_derives_a_positive_search_witness
#print axioms active_half_order_bound_derives_a_positive_search_witness
set_option pp.all true in
#check @leastPositiveExponent
#print axioms leastPositiveExponent
set_option pp.all true in
#check @derived_least_positive_exponent_has_exact_search_bounds_and_power
#print axioms derived_least_positive_exponent_has_exact_search_bounds_and_power
set_option pp.all true in
#check @every_earlier_positive_power_before_the_derived_index_is_not_one
#print axioms every_earlier_positive_power_before_the_derived_index_is_not_one
set_option pp.all true in
#check @nonunit_active_residue_has_a_negative_half_power_at_its_derived_index
#print axioms nonunit_active_residue_has_a_negative_half_power_at_its_derived_index
end ShielddSecurity.TransferFfLeastPower01
