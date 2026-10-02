import ShielddSecurity.SpendGateInputs
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring.RingNF
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 400000
namespace ShielddSecurity

variable {F : Type} [Field F]


theorem square_zero (x : F) (h : Square x 0) : x = 0 := by
  exact (mul_self_eq_zero.mp h)


/-- The compiler's outlined private constant is constrained, never assumed. -/
theorem outlined_one (one copy : F) (hOne : one = 1)
    (row : Square (one - copy) 0) : copy = 1 := by
  have h := sub_eq_zero.mp (square_zero _ row)
  exact h.symm.trans hOne

/-- Two deferred square expressions retain both sides of their equality. -/
theorem deferred_square (x y auxiliary : F)
    (left : Square x auxiliary) (right : Square y auxiliary) : x*x = y*y := by
  exact left.trans right.symm

/-- The two square rows used for a non-square product enforce that product. -/
theorem product_encoding (x y difference product : F) (four : (4 : F) ≠ 0)
    (minus : Square (x-y) difference)
    (plus : Square (x+y) (difference + 4*product)) : x*y = product := by
  apply mul_left_cancel₀ four
  calc
    4*(x*y) = (x+y)*(x+y) - (x-y)*(x-y) := by ring
    _ = 4*product := by rw [plus, minus]; ring

def binary : List Bool → Nat
  | [] => 0
  | bit :: bits => (if bit then 1 else 0) + 2 * binary bits

def fieldBinary : List F → F
  | [] => 0
  | bit :: bits => bit + 2 * fieldBinary bits

theorem binary_bound (bits : List Bool) : binary bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [binary]
  | cons bit bits ih =>
      cases bit <;> simp only [binary, List.length_cons, Bool.false_eq_true, ↓reduceIte, Nat.pow_succ] <;> omega

theorem binary_cast (bits : List Bool) :
    fieldBinary (bits.map (fun b => if b then (1 : F) else 0)) = (binary bits : F) := by
  induction bits with
  | nil => simp [fieldBinary, binary]
  | cons bit bits ih => cases bit <;> simp [fieldBinary, binary, ih, Nat.cast_add, Nat.cast_mul]

def encodeBits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, n => decide (n % 2 = 1) :: encodeBits width (n / 2)

@[simp] theorem encodeBits_length (width n : Nat) : (encodeBits width n).length = width := by
  induction width generalizing n <;> simp_all [encodeBits]

theorem encodeBits_value (width n : Nat) (bound : n < 2^width) :
    binary (encodeBits width n) = n := by
  induction width generalizing n with
  | zero =>
      have hn : n = 0 := by simpa using bound
      simp [encodeBits, binary, hn]
  | succ width ih =>
      have half : n / 2 < 2^width := by
        have h : n < 2^width * 2 := by simpa [Nat.pow_succ] using bound
        omega
      simp only [encodeBits, binary, ih (n / 2) half, decide_eq_true_eq]
      split <;> omega

/-- Any satisfying bit assignment has an independent bounded integer meaning. -/
theorem range_sound (xs : List F) (value : F)
    (bits : ∀ x ∈ xs, Square x x) (reconstruction : fieldBinary xs = value) :
    ∃ n : Nat, n < 2 ^ xs.length ∧ (n : F) = value := by
  classical
  let decoded := xs.map (fun x => decide (x = 1))
  have map_eq : decoded.map (fun b => if b then (1 : F) else 0) = xs := by
    apply List.ext_getElem
    · simp [decoded]
    · intro i hi hj
      simp only [decoded, List.getElem_map]
      rcases boolean_sound (xs[i]) (bits _ (List.getElem_mem hj)) with h | h
      · simp [h]
      · simp [h]
  refine ⟨binary decoded, ?_, ?_⟩
  · simpa [decoded] using binary_bound decoded
  · rw [← binary_cast decoded, map_eq, reconstruction]

/-- Honest bit encodings satisfy the same boolean and reconstruction relation. -/
theorem range_completeness (bits : List Bool) :
    (∀ x ∈ bits.map (fun b => if b then (1 : F) else 0), Square x x) ∧
    fieldBinary (bits.map (fun b => if b then (1 : F) else 0)) = (binary bits : F) := by
  constructor
  · intro x hx
    rcases List.mem_map.mp hx with ⟨b, _, rfl⟩
    cases b <;> simp [Square]
  · exact binary_cast bits

#print axioms boolean_sound
#print axioms range_sound
#print axioms range_completeness
#print axioms outlined_one
#print axioms deferred_square
#print axioms product_encoding
end ShielddSecurity
