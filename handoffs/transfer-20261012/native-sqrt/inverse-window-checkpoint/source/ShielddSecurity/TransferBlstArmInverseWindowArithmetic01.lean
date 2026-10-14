import Init.Data.Nat.Bitwise.Lemmas
import Mathlib.Tactic.Ring
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowArithmetic01

/-! Mac import-minimized replay variant of the desktop handwritten draft. These symbolic quotient identities support the
common high-window proof. They do not establish the runtime's selected limb,
CLZ value, register shifts, or correspondence to a complete packed input. -/

theorem symbolic_packed_prefix_division_removes_the_entire_lower_tail
    (base quotient tail : Nat) (positive : 0 < base) (bounded : tail < base) :
    (base * quotient + tail) / base = quotient := by
  rw [Nat.add_comm, Nat.add_mul_div_left tail quotient positive,
    Nat.div_eq_of_lt bounded, zero_add]

theorem symbolic_two_limb_window_division_is_exact_without_a_tail_premise
    (radix scale divisor high low : Nat) (positive : 0 < divisor)
    (factorization : radix = scale * divisor) :
    (radix * high + low) / divisor = scale * high + low / divisor := by
  rw [factorization]
  have rearranged : (scale * divisor) * high + low = low + divisor * (scale * high) := by
    ring
  rw [rearranged, Nat.add_mul_div_left low (scale * high) positive, Nat.add_comm]

theorem symbolic_whole_input_window_division_removes_all_lower_limbs
    (base radix scale divisor high low tail : Nat)
    (basePositive : 0 < base) (divisorPositive : 0 < divisor)
    (tailBound : tail < base) (factorization : radix = scale * divisor) :
    (base * (radix * high + low) + tail) / (base * divisor) =
      scale * high + low / divisor := by
  rw [← Nat.div_div_eq_div_mul,
    symbolic_packed_prefix_division_removes_the_entire_lower_tail
      base (radix * high + low) tail basePositive tailBound]
  exact symbolic_two_limb_window_division_is_exact_without_a_tail_premise
    radix scale divisor high low divisorPositive factorization

theorem symbolic_disjoint_window_fragments_have_exact_or_sum
    (shift high fragment : Nat) (bounded : fragment < 2 ^ shift) :
    (2 ^ shift * high ||| fragment) = 2 ^ shift * high + fragment := by
  exact (Nat.two_pow_add_eq_or_of_lt bounded high).symm

set_option pp.all true in
#check @symbolic_packed_prefix_division_removes_the_entire_lower_tail
#print axioms symbolic_packed_prefix_division_removes_the_entire_lower_tail
set_option pp.all true in
#check @symbolic_two_limb_window_division_is_exact_without_a_tail_premise
#print axioms symbolic_two_limb_window_division_is_exact_without_a_tail_premise
set_option pp.all true in
#check @symbolic_whole_input_window_division_removes_all_lower_limbs
#print axioms symbolic_whole_input_window_division_removes_all_lower_limbs
set_option pp.all true in
#check @symbolic_disjoint_window_fragments_have_exact_or_sum
#print axioms symbolic_disjoint_window_fragments_have_exact_or_sum
end ShielddSecurity.TransferBlstArmInverseWindowArithmetic01
