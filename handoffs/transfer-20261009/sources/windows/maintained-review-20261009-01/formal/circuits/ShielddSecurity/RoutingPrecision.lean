import ShielddSecurity.Scalar

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.RoutingPrecision

variable {F : Type} [Field F] [DecidableEq F]

/-- These are the two assertions in range::is_zero; no inverse-at-zero
uniqueness is asserted, since the runtime does not constrain that value. -/
theorem zero_test_sound (value inverse flag : F)
    (unit : value * inverse = 1 - flag) (annihilate : value * flag = 0) :
    flag = if value = 0 then 1 else 0 := by
  by_cases exceptional : value = 0
  · have h : 1 - flag = 0 := by simpa only [exceptional, zero_mul] using unit.symm
    simpa only [if_pos exceptional] using (sub_eq_zero.mp h).symm
  · have h : flag = 0 := (mul_eq_zero.mp annihilate).resolve_left exceptional
    simpa only [if_neg exceptional] using h

def indicator (value : F) : F := if value = 0 then 1 else 0

/-- The native zero case may use any inverse; the canonical constructor
chooses the field inverse, whose value at zero is zero. -/
theorem zero_test_complete (value : F) :
    Square (indicator value) (indicator value) ∧
      value * value⁻¹ = 1 - indicator value ∧ value * indicator value = 0 := by
  by_cases exceptional : value = 0
  · simp [indicator, exceptional, Square]
  · simp [indicator, exceptional, Square, mul_inv_cancel₀ exceptional]

def sum : List F → F
  | [] => 0
  | head :: tail => head + sum tail

private theorem sum_map_zero (indices : List Nat) (values : Nat → F)
    (zero : ∀ index ∈ indices, values index = 0) :
    sum (indices.map values) = 0 := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      have first := zero head (by simp)
      have rest := ih (by intro index member; exact zero index (by simp [member]))
      simp only [List.map_cons, sum, first, rest, zero_add]

/-- Onehot is an actual separate row. Together with the two zero-test
equations it derives domain membership, without a promised precision bound. -/
theorem onehot_sound (value : F) (indices : List Nat) (flags inverse : Nat → F)
    (unit : ∀ index ∈ indices, (value - (index : F)) * inverse index = 1 - flags index)
    (annihilate : ∀ index ∈ indices, (value - (index : F)) * flags index = 0)
    (onehot : sum (indices.map flags) = 1) :
    ∃ index ∈ indices, value = (index : F) := by
  classical
  by_contra absent
  have zero : ∀ index ∈ indices, flags index = 0 := by
    intro index member
    have different : value - (index : F) ≠ 0 := by
      intro equality
      exact absent ⟨index, member, sub_eq_zero.mp equality⟩
    have flag := zero_test_sound (value - (index : F)) (inverse index) (flags index)
      (unit index member) (annihilate index member)
    simpa only [if_neg different] using flag
  have impossible : (0 : F) = 1 := (sum_map_zero indices flags zero).symm.trans onehot
  exact zero_ne_one impossible

/-- Specializing the exact 33 source tests derives the legal integer domain. -/
theorem precision_sound (value : F) (flags inverse : Nat → F)
    (unit : ∀ index ∈ List.range 33,
      (value - (index : F)) * inverse index = 1 - flags index)
    (annihilate : ∀ index ∈ List.range 33,
      (value - (index : F)) * flags index = 0)
    (onehot : sum ((List.range 33).map flags) = 1) :
    ∃ index : Nat, index < 33 ∧ value = (index : F) := by
  obtain ⟨index, member, equality⟩ := onehot_sound value (List.range 33) flags inverse unit annihilate onehot
  exact ⟨index, List.mem_range.mp member, equality⟩

/-- The observed prefixes are linear sums of the same derived selectors.
This transports their captured LC equalities without changing the assignment. -/
theorem prefix_sound (value : F) (indices : List Nat) (flags inverse : Nat → F)
    (prefixValue : F) (unit : ∀ index ∈ indices,
      (value - (index : F)) * inverse index = 1 - flags index)
    (annihilate : ∀ index ∈ indices, (value - (index : F)) * flags index = 0)
    (sourceSum : prefixValue = sum (indices.map flags)) :
    prefixValue = sum (indices.map (fun (index : Nat) => indicator (value - (index : F)))) := by
  rw [sourceSum]
  congr 1
  apply List.map_congr_left
  intro index member
  exact zero_test_sound _ _ _ (unit index member) (annihilate index member)

private theorem sum_indicator (indices : List Nat) (target : Nat)
    (unique : indices.Nodup) (present : target ∈ indices) :
    sum (indices.map (fun (index : Nat) => if index = target then (1 : F) else 0)) = 1 := by
  induction indices with
  | nil => simp only [List.not_mem_nil] at present
  | cons head tail ih =>
      obtain ⟨outside, tailUnique⟩ := List.nodup_cons.mp unique
      by_cases same : head = target
      · have zero : ∀ index ∈ tail, (if index = target then (1 : F) else 0) = 0 := by
          intro index member
          have different : index ≠ target := by
            intro equality
            exact outside (by simpa only [same, equality] using member)
          exact if_neg different
        have rest := sum_map_zero tail (fun (index : Nat) => if index = target then (1 : F) else 0) zero
        simp only [List.map_cons, sum, if_pos same, rest, add_zero]
      · have inside : target ∈ tail := by
          rcases List.mem_cons.mp present with equal | member
          · exact False.elim (same equal.symm)
          · exact member
        have rest := ih tailUnique inside
        simp only [List.map_cons, sum, if_neg same, rest, zero_add]

/-- A legal native precision constructs the onehot row independently of any
satisfying assignment. All 33 tests use the same field value. -/
theorem onehot_complete [CharP F Scalar.modulus] (precision : Nat) (legal : precision < 33) :
    sum ((List.range 33).map (fun (index : Nat) => indicator ((precision : F) - (index : F)))) = 1 := by
  have capacity : 33 < Scalar.modulus := by decide
  have pointwise : ∀ index ∈ List.range 33,
      indicator ((precision : F) - (index : F)) = (if index = precision then 1 else 0) := by
    intro index member
    have bounded := (List.mem_range.mp member).trans capacity
    have meaning : (precision : F) - (index : F) = 0 ↔ index = precision := by
      constructor
      · intro equality
        exact (bounded_cast_injective (legal.trans capacity) bounded (sub_eq_zero.mp equality)).symm
      · intro equality
        simp only [equality, sub_self]
    simp only [indicator, meaning]
  have mapped := List.map_congr_left pointwise
  rw [mapped]
  exact sum_indicator (List.range 33) precision (List.nodup_range) (List.mem_range.mpr legal)

set_option pp.all true in
#check @zero_test_sound
#print axioms zero_test_sound
set_option pp.all true in
#check @zero_test_complete
#print axioms zero_test_complete
set_option pp.all true in
#check @onehot_sound
#print axioms onehot_sound
set_option pp.all true in
#check @precision_sound
#print axioms precision_sound
set_option pp.all true in
#check @prefix_sound
#print axioms prefix_sound
set_option pp.all true in
#check @onehot_complete
#print axioms onehot_complete

end ShielddSecurity.RoutingPrecision
