import ShielddSecurity.NativeAssetHashParameters
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEncryptionFixedArithmetic

/- Small integer certificates for the two fixed, empty-input audit hashes.
The generated instances must check every actual parameter and every transition.
The recurrence below does not expand a 65-round expression tree. -/

def integerInitial (width domain : Nat) : Fin width → Int :=
  fun column => if column.val = 0 then (domain : Int) else 0

def integerRound {width : Nat} (parameters : Poseidon.Parameters Int width)
    (index : Nat) (state : Fin width → Int) : Fin width → Int :=
  fun row => ((List.finRange width).foldl (fun total column =>
    let shifted := state column + parameters.ark index column
    let transformed := if Poseidon.nonlinear index column.val then shifted ^ 5 else shifted
    total + parameters.mds row column * transformed) 0) % (Scalar.modulus : Int)

variable {F : Type} [Field F] [CharP F Scalar.modulus]

private theorem fold_cast {I : Type} (items : List I) (term : I → Int) (initial : Int) :
    ((items.foldl (fun total item => total + term item) initial : Int) : F) =
      items.foldl (fun total item => total + (term item : F)) (initial : F) := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.foldl_cons, Int.cast_add] using ih (initial + term head)

theorem round_value {width : Nat} (parameters : Poseidon.Parameters Int width)
    (index : Nat) (state : Fin width → Int) :
    (fun column => (integerRound parameters index state column : F)) =
      Poseidon.round (Poseidon.castParameters parameters) index
        (fun column => (state column : F)) := by
  funext row
  unfold integerRound
  rw [Compiler.coefficient_mod (p := Scalar.modulus)]
  rw [fold_cast]
  simp only [Int.cast_zero, Poseidon.round, Poseidon.mix, Poseidon.castParameters]
  congr 1
  funext total column
  split <;> simp only [Int.cast_add, Int.cast_mul, Int.cast_pow]

/-- The premises are individual finite arithmetic transitions, each checked in
the generated instance. No complete hash result is supplied as a premise. -/
theorem empty_hash_trace (parameters : Poseidon.Parameters Int 3)
    (domain : Nat) (states : Nat → Fin 3 → Int)
    (initial : states 0 = integerInitial 3 domain)
    (steps : ∀ index, index < 65 →
      states (index + 1) = integerRound parameters index (states index)) :
    Poseidon.hash3 (Poseidon.castParameters parameters) domain [] =
      (states 65 ⟨1, by decide⟩ : F) := by
  have chain := Poseidon.rounds_chain (Poseidon.castParameters parameters)
    (fun index column => (states index column : F)) 65 (by
      intro index bounded
      dsimp only
      rw [steps index bounded]
      exact round_value parameters index (states index))
  have starting : (fun column => (states 0 column : F)) =
      Poseidon.initial (width := 3) domain 0 := by
    rw [initial]
    funext column
    simp only [integerInitial, Poseidon.initial, Nat.zero_mul, Nat.zero_add]
    split <;> simp only [Int.cast_natCast, Int.cast_zero]
  change Poseidon.rounds (Poseidon.castParameters parameters) 65
    (Poseidon.initial domain 0) ⟨1, by decide⟩ = _
  rw [← starting, ← chain]

/-- This public interface fixes the actual small parameter table used by the
owned native loader. It adds no caller-selected parameter or hash-result law. -/
theorem fixed_empty_hash_trace (domain : Nat) (states : Nat → Fin 3 → Int)
    (initial : states 0 = integerInitial 3 domain)
    (steps : ∀ index, index < 65 →
      states (index + 1) = integerRound
        RuntimeHashBlock_authorization_rnk_permutation2_0.parameters index (states index)) :
    Poseidon.hash3 NativeAssetHashParameters.smallParameters domain [] =
      (states 65 ⟨1, by decide⟩ : F) :=
  empty_hash_trace RuntimeHashBlock_authorization_rnk_permutation2_0.parameters
    domain states initial steps

/-- A checked modular product supplies an inverse, including the nonzero
obligation. This is a primitive arithmetic certificate, not a map-result law. -/
theorem inverse_value (value inverse : Int)
    (product : (value * inverse) % (Scalar.modulus : Int) = 1) :
    (value : F)⁻¹ = (inverse : F) := by
  have equation : (value : F) * (inverse : F) = 1 := by
    have cast := Compiler.coefficient_mod (F := F) (p := Scalar.modulus) (value * inverse)
    rw [product] at cast
    simpa only [Int.cast_one, Int.cast_mul] using cast.symm
  have nonzero : (value : F) ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at equation
    exact zero_ne_one equation
  apply mul_left_cancel₀ nonzero
  rw [mul_inv_cancel₀ nonzero, equation]

theorem cast_nonzero (value : Nat) (positive : 0 < value)
    (bounded : value < Scalar.modulus) : (value : F) ≠ 0 := by
  intro zero
  have equal := bounded_cast_injective (F := F) (p := Scalar.modulus)
    bounded (by decide : 0 < Scalar.modulus) (by simpa only [Nat.cast_zero] using zero)
  omega

set_option pp.all true in
#check @round_value
#print axioms round_value
set_option pp.all true in
#check @empty_hash_trace
#print axioms empty_hash_trace
set_option pp.all true in
#check @fixed_empty_hash_trace
#print axioms fixed_empty_hash_trace
set_option pp.all true in
#check @inverse_value
#print axioms inverse_value
set_option pp.all true in
#check @cast_nonzero
#print axioms cast_nonzero

end ShielddSecurity.NativeEncryptionFixedArithmetic
