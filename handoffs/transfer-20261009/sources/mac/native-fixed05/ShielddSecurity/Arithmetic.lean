import ShielddSecurity.Range
import Mathlib.Algebra.CharP.Defs

set_option maxHeartbeats 400000
namespace ShielddSecurity
variable {F : Type} [Field F] {p : Nat} [CharP F p]

/-- Replacing a canonical coefficient by its signed representative preserves evaluation. -/
theorem signed_coefficient (n : Nat) : (((n : Int) - (p : Int) : Int) : F) = (n : F) := by
  simp [Int.cast_sub, CharP.cast_eq_zero F p]

theorem bounded_cast_injective {a b : Nat} (ha : a < p) (hb : b < p)
    (h : (a : F) = (b : F)) : a = b := by
  have eq := (CharP.cast_eq_iff_mod_eq F p).mp h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using eq

/-- Range bounds supplied by caller constraints make modular addition integer addition. -/
theorem addition_lift {bound prior outbound candidate : Nat}
    (capacity : 2 * bound ≤ p)
    (priorBound : prior < bound) (outboundBound : outbound < bound)
    (candidateBound : candidate < bound)
    (fieldEquation : (prior : F) + (outbound : F) = (candidate : F)) :
    prior + outbound = candidate := by
  apply bounded_cast_injective (F := F) (p := p) (by omega) (by omega)
  simpa using fieldEquation

/-- The bounded-difference comparator has the intended integer order in either branch. -/
theorem comparison_lift {bound a b difference : Nat} (borrow : Bool)
    (capacity : 2 * bound ≤ p) (aBound : a < bound) (bBound : b < bound)
    (differenceBound : difference < bound)
    (equation : (b : F) - (a : F) = (difference : F) - (if borrow then (bound : F) else 0)) :
    borrow = false ↔ a ≤ b := by
  have rearranged : (b : F) + (if borrow then (bound : F) else 0) =
      (difference : F) + (a : F) := by
    calc
      _ = ((b : F) - (a : F)) + (a : F) + (if borrow then (bound : F) else 0) := by ring
      _ = _ := by rw [equation]; ring
  cases borrow with
  | false =>
      have hb : b = difference + a := bounded_cast_injective (F := F) (p := p)
        (by omega) (by omega) (by simpa using rearranged)
      simp
      omega
  | true =>
      have hb : b + bound = difference + a := bounded_cast_injective (F := F) (p := p)
        (by omega) (by omega) (by simpa using rearranged)
      simp
      omega

#print axioms addition_lift
#print axioms comparison_lift
end ShielddSecurity

set_option pp.all true in
#check @ShielddSecurity.addition_lift
set_option pp.all true in
#check @ShielddSecurity.comparison_lift
