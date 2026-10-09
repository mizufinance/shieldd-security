import ShielddSecurity.TransferReduction
import Mathlib.Algebra.Order.Ring.Defs

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReducedKeyCounting

-- The cached rational arithmetic already supplies these elementary ordered-ring
-- facts; keep their derived instance local to the finite counting argument.
local instance : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ inequality _ => Rat.add_le_add_right.2 inequality

local instance : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ positiveLeft positiveRight ↦
  (Rat.mul_nonneg positiveLeft.le positiveRight.le).lt_of_ne'
    (mul_ne_zero positiveLeft.ne' positiveRight.ne')

/-- Canonical field outputs before any caller filtering of zero IVKs. The pinned
FVK constructor rejects zero reduction; it does not retry internally.
This finite counting model does not assert that the concrete Poseidon function
is a random oracle or that distinct ownership inputs have distinct IVKs. -/
abbrev Output := Fin Scalar.modulus
abbrev Fiber (scalar : Nat) := {value : Output // value.val % Scalar.order = scalar}

theorem quotient_bound (value : Output) : value.val / Scalar.order < 9 := by
  have division := Nat.mod_add_div value.val Scalar.order
  have bounded := value.isLt
  simp only [Scalar.modulus, Scalar.order] at division bounded ⊢
  omega

def quotientIndex (scalar : Nat) (value : Fiber scalar) : Fin 9 :=
  ⟨value.val.val / Scalar.order, quotient_bound value.val⟩

theorem quotient_injective (scalar : Nat) : Function.Injective (quotientIndex scalar) := by
  intro first second same
  have quotients : first.val.val / Scalar.order = second.val.val / Scalar.order :=
    congrArg Fin.val same
  have left := Nat.mod_add_div first.val.val Scalar.order
  have right := Nat.mod_add_div second.val.val Scalar.order
  rw [first.property, quotients] at left
  rw [second.property] at right
  exact Subtype.ext (Fin.ext (left.symm.trans right))

theorem fiber_card_le_nine (scalar : Nat) : Fintype.card (Fiber scalar) ≤ 9 := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (quotientIndex scalar) (quotient_injective scalar)

def zeroFiberEquiv : Fiber 0 ≃ Fin 9 where
  toFun := quotientIndex 0
  invFun quotient := ⟨⟨quotient.val * Scalar.order, by
    have bounded := quotient.isLt
    simp only [Scalar.modulus, Scalar.order] at *
    omega⟩, by simp⟩
  left_inv value := by
    apply Subtype.ext
    apply Fin.ext
    have division := Nat.mod_add_div value.val.val Scalar.order
    rw [value.property] at division
    simpa only [zero_add, Nat.mul_comm] using division
  right_inv quotient := by
    apply Fin.ext
    exact Nat.mul_div_left quotient.val (by decide : 0 < Scalar.order)

theorem zero_fiber_card : Fintype.card (Fiber 0) = 9 :=
  (Fintype.card_congr zeroFiberEquiv).trans (Fintype.card_fin 9)

abbrev NonzeroOutput := {value : Output // ¬ value.val % Scalar.order = 0}

theorem nonzero_output_card : Fintype.card NonzeroOutput = Scalar.modulus - 9 := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  exact congrArg (fun count => Scalar.modulus - count) zero_fiber_card

/-- This is the exact fraction for a uniformly sampled canonical field output.
An ownership-game theorem must separately supply its fresh-query distribution,
domain encoding, group preconditions, extraction and adaptive query accounting. -/
def uniformHitFraction (scalar : Nat) : ℚ :=
  (Fintype.card (Fiber scalar) : ℚ) / (Scalar.modulus : ℚ)

theorem uniform_hit_bound (scalar : Nat) :
    uniformHitFraction scalar ≤ 9 / (Scalar.modulus : ℚ) := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast fiber_card_le_nine scalar)
    (by norm_num [Scalar.modulus])

theorem uniform_zero_fraction : uniformHitFraction 0 = 9 / (Scalar.modulus : ℚ) := by
  simp only [uniformHitFraction, zero_fiber_card, Nat.cast_ofNat]

set_option pp.all true in
#check @quotient_bound
#print axioms quotient_bound
set_option pp.all true in
#check @quotient_injective
#print axioms quotient_injective
set_option pp.all true in
#check @fiber_card_le_nine
#print axioms fiber_card_le_nine
set_option pp.all true in
#check @zeroFiberEquiv
#print axioms zeroFiberEquiv
set_option pp.all true in
#check @zero_fiber_card
#print axioms zero_fiber_card
set_option pp.all true in
#check @nonzero_output_card
#print axioms nonzero_output_card
set_option pp.all true in
#check @uniform_hit_bound
#print axioms uniform_hit_bound
set_option pp.all true in
#check @uniform_zero_fraction
#print axioms uniform_zero_fraction

end ShielddSecurity.TransferReducedKeyCounting
