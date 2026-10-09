import ShielddSecurity.ScalarBits

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.RoutingTagSemantics

theorem binary_div_two (head : Bool) (tail : List Bool) :
    binary (head :: tail) / 2 = binary tail := by
  cases head <;> simp [binary, Nat.add_mul_div_left]

/-- Integer bit extraction follows the symbolic little-endian recurrence,
including zero bits beyond the list. -/
theorem binary_bit (bits : List Bool) (index : Nat) :
    binary bits / 2^index % 2 = if bits.getD index false then 1 else 0 := by
  induction bits generalizing index with
  | nil => simp [binary, List.getD]
  | cons head tail ih =>
      cases index with
      | zero =>
          cases head <;> simp [binary, List.getD, Nat.add_mod, Nat.mul_mod]
      | succ index =>
          rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, binary_div_two]
          simpa only [List.getD_cons_succ] using ih index

/-- The pointwise selector equations are separate row-proof obligations.
Their composition derives the independent integer tag-bit equation. -/
theorem selected_bits (output route random : List Bool) (select : Nat → Bool)
    (pointwise : ∀ bit : Fin 32, output.getD bit.val false =
      if select bit.val then route.getD bit.val false else random.getD bit.val false) :
    ∀ bit : Fin 32, binary output / 2^bit.val % 2 =
      (if select bit.val then binary route else binary random) / 2^bit.val % 2 := by
  intro bit
  rw [binary_bit, pointwise bit]
  cases selected : select bit.val with
  | false => exact (binary_bit random bit.val).symm
  | true => exact (binary_bit route bit.val).symm

theorem tag_semantics (output route random : List Bool) (select : Nat → Bool)
    (width : output.length = 32) (tag : Nat) (reconstruction : tag = binary output)
    (pointwise : ∀ bit : Fin 32, output.getD bit.val false =
      if select bit.val then route.getD bit.val false else random.getD bit.val false) :
    tag < 2^32 ∧ ∀ bit : Fin 32, tag / 2^bit.val % 2 =
      (if select bit.val then binary route else binary random) / 2^bit.val % 2 := by
  rw [reconstruction]
  exact ⟨by simpa only [width] using binary_bound output,
    selected_bits output route random select pointwise⟩

set_option pp.all true in
#check @binary_div_two
#print axioms binary_div_two
set_option pp.all true in
#check @binary_bit
#print axioms binary_bit
set_option pp.all true in
#check @selected_bits
#print axioms selected_bits
set_option pp.all true in
#check @tag_semantics
#print axioms tag_semantics

end ShielddSecurity.RoutingTagSemantics
