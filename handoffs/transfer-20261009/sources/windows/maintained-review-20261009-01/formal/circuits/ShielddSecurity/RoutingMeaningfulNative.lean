import ShielddSecurity.ScalarBits

set_option maxHeartbeats 200000

namespace ShielddSecurity.RoutingMeaningfulNative

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- A bounded amount cannot become zero through field reduction. The bound
and the source-to-field equality must come from their independent joins. -/
theorem amount_zero_iff (amount : Nat) (bounded : amount < Scalar.modulus) :
    (amount : F) = 0 ↔ amount = 0 := by
  constructor
  · intro zero
    have capacity : 0 < Scalar.modulus := by decide
    exact bounded_cast_injective bounded capacity (by simpa only [Nat.cast_zero] using zero)
  · intro zero
    simp only [zero, Nat.cast_zero]

theorem change_bit [DecidableEq F] (amount : Nat) (bounded : amount < Scalar.modulus)
    (value : F) (source : value = (amount : F)) :
    decide (value ≠ 0) = (amount != 0) := by
  rw [source]
  have zero := amount_zero_iff (F := F) amount bounded
  by_cases absent : amount = 0
  · simp [absent]
  · have nonzero : (amount : F) ≠ 0 := fun equality => absent (zero.mp equality)
    simp [absent, nonzero]

/-- Slot zero is the receiver slot exactly when the permutation bit is set. -/
theorem meaningful_slot0 (swapped regulated : Bool) (amount : Nat) :
    (!decide (if swapped then (0 : Nat) = 1 else 0 = 0) || regulated || (amount != 0)) =
      (swapped || (regulated || (amount != 0))) := by
  cases swapped <;> simp

/-- Slot one has the complementary sender/receiver choice. -/
theorem meaningful_slot1 (swapped regulated : Bool) (amount : Nat) :
    (!decide (if swapped then (1 : Nat) = 1 else 1 = 0) || regulated || (amount != 0)) =
      (!swapped || (regulated || (amount != 0))) := by
  cases swapped <;> simp

set_option pp.all true in
#check @amount_zero_iff
#print axioms amount_zero_iff
set_option pp.all true in
#check @change_bit
#print axioms change_bit
set_option pp.all true in
#check @meaningful_slot0
#print axioms meaningful_slot0
set_option pp.all true in
#check @meaningful_slot1
#print axioms meaningful_slot1

end ShielddSecurity.RoutingMeaningfulNative
