import ShielddSecurity.ScalarComparisonBounds
import Mathlib.Data.Fintype.Card

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferReduction
open ScalarComparisonBounds

/-- Imported functional contract for the pinned prime-field canonical codec.
CharP alone does not provide this interface for extension fields. This is an
explicit theorem parameter; native codec agreement is a separate source join. -/
structure CanonicalField (F : Type) [Field F] where
  decode : F → Nat
  bounded : ∀ value, decode value < Scalar.modulus
  roundtrip : ∀ value, ((decode value : Nat) : F) = value

theorem decode_canonical_cast {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : CanonicalField F) (n : Nat) (bounded : n < Scalar.modulus) :
    codec.decode (n : F) = n := by
  exact Scalar.canonical_representative_unique (n : F) (codec.decode (n : F)) n
    (codec.bounded _) bounded (codec.roundtrip _) rfl

/-- The explicit canonical codec excludes larger extension fields. -/
def codec_equiv {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : CanonicalField F) : F ≃ Fin Scalar.modulus where
  toFun value := ⟨codec.decode value, codec.bounded value⟩
  invFun value := (value.val : F)
  left_inv := codec.roundtrip
  right_inv value := Fin.ext (decode_canonical_cast codec value.val value.isLt)

theorem codec_cardinality {F : Type} [Field F] [CharP F Scalar.modulus] [Fintype F]
    (codec : CanonicalField F) : Fintype.card F = Scalar.modulus := by
  exact (Fintype.card_congr (codec_equiv codec)).trans (Fintype.card_fin Scalar.modulus)

theorem decoded_reduction {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : CanonicalField F) (hash quotient remainder : F) (q r : Nat)
    (qBound : q ≤ 8) (positive : 0 < r) (rBound : r < Scalar.order)
    (sumBound : q * Scalar.order + r < Scalar.modulus)
    (qCast : (q : F) = quotient) (rCast : (r : F) = remainder)
    (hashCast : ((q * Scalar.order + r : Nat) : F) = hash) :
    codec.decode quotient ≤ 8 ∧ 0 < codec.decode remainder ∧
      codec.decode remainder < Scalar.order ∧
      codec.decode hash = codec.decode remainder + Scalar.order * codec.decode quotient := by
  have qSmall : q < Scalar.modulus := by simp only [Scalar.modulus] at *; omega
  have rSmall : r < Scalar.modulus := by
    have capacity : Scalar.order < Scalar.modulus := by decide
    exact rBound.trans capacity
  have qDecode : codec.decode quotient = q := by
    rw [← qCast]
    exact decode_canonical_cast codec q qSmall
  have rDecode : codec.decode remainder = r := by
    rw [← rCast]
    exact decode_canonical_cast codec r rSmall
  have hashDecode : codec.decode hash = q * Scalar.order + r := by
    rw [← hashCast]
    exact decode_canonical_cast codec _ sumBound
  rw [qDecode, rDecode, hashDecode]
  exact ⟨qBound, positive, rBound, by ac_rfl⟩

theorem endpoint_append (initial : Linear) (front back : List ScalarRows.StepData) :
    endpoint initial (front ++ back) = endpoint (endpoint initial front) back := by
  induction front generalizing initial with
  | nil => rfl
  | cons step tail ih => exact ih step.after

theorem checked_private_remainder {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (steps : List ScalarRows.StepData) (remainder : Linear)
    (bits : ScalarBits.checkBits Scalar.modulus rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain Scalar.modulus rows [(0, 1)] steps = true)
    (ending : checkEquality Scalar.modulus rows (endpoint [(0, 1)] steps) [(0, 1)] = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.order - 1)
    (rebuild : checkEquality Scalar.modulus rows
      (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) remainder = true) :
    ∃ r : Nat, r < Scalar.order ∧ (r : F) = eval rho remainder := by
  have bound := checked_remainder_bound rho one four rows satisfied steps bits chain ending maximum
  have decoded := ScalarBits.decoded_bits_value rho rows satisfied
    (steps.map ScalarRows.StepData.left) bits
  have rebuilt := checked_equality rho rows satisfied _ remainder rebuild
  exact ⟨_, bound, decoded.symm.trans rebuilt⟩

/-- Separate actual witness reconstruction assertions are essential: the
runtime does not contain a fabricated bit-linear equation row. Comparator
bounds and inverse soundness remain separate prerequisites to this join. -/
theorem checked_role_equation {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (rows : List Row) (satisfied : Satisfies rho rows)
    (qBits rBits : List Linear) (qRole rRole hash : Linear)
    (qBoolean : ScalarBits.checkBits Scalar.modulus rows qBits = true)
    (rBoolean : ScalarBits.checkBits Scalar.modulus rows rBits = true)
    (qRebuild : checkEquality Scalar.modulus rows (ScalarBits.bitLinear qBits) qRole = true)
    (rRebuild : checkEquality Scalar.modulus rows (ScalarBits.bitLinear rBits) rRole = true)
    (equation : checkEquality Scalar.modulus rows
      (scaleLinear (Scalar.order : Int) qRole ++ rRole) hash = true) :
    let q := binary (ScalarBits.decodeBits rho qBits)
    let r := binary (ScalarBits.decodeBits rho rBits)
    (q : F) * (Scalar.order : F) + (r : F) = eval rho hash := by
  have qValue := ScalarBits.decoded_bits_value rho rows satisfied qBits qBoolean
  have rValue := ScalarBits.decoded_bits_value rho rows satisfied rBits rBoolean
  have qEq := checked_equality rho rows satisfied _ qRole qRebuild
  have rEq := checked_equality rho rows satisfied _ rRole rRebuild
  have eq := checked_equality rho rows satisfied _ hash equation
  rw [eval_append, eval_scale] at eq
  rw [← qEq, ← rEq, qValue, rValue] at eq
  simpa only [Int.cast_ofNat, Int.cast_natCast, mul_comm] using eq

theorem checked_inverse_nonzero {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (inverse consumer output : Linear) (data : ScalarRows.ProductData)
    (product : ScalarRows.checkProduct Scalar.modulus rows inverse consumer output data = true)
    (assertion : checkEquality Scalar.modulus rows output [(0, 1)] = true) :
    eval rho consumer ≠ 0 := by
  have multiplied := ScalarRows.checked_product_sound rho one four rows satisfied
    inverse consumer output data product
  have asserted := checked_equality rho rows satisfied output [(0, 1)] assertion
  have nonzero : eval rho inverse * eval rho consumer = 1 := by
    simpa [eval, one] using multiplied.symm.trans asserted
  intro zero
  rw [zero, mul_zero] at nonzero
  exact zero_ne_one nonzero


end ShielddSecurity.TransferReduction

set_option pp.all true in
#check @ShielddSecurity.TransferReduction.CanonicalField
#print axioms ShielddSecurity.TransferReduction.CanonicalField
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.decode_canonical_cast
#print axioms ShielddSecurity.TransferReduction.decode_canonical_cast
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.codec_equiv
#print axioms ShielddSecurity.TransferReduction.codec_equiv
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.codec_cardinality
#print axioms ShielddSecurity.TransferReduction.codec_cardinality
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.decoded_reduction
#print axioms ShielddSecurity.TransferReduction.decoded_reduction
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.endpoint_append
#print axioms ShielddSecurity.TransferReduction.endpoint_append
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.checked_private_remainder
#print axioms ShielddSecurity.TransferReduction.checked_private_remainder
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.checked_role_equation
#print axioms ShielddSecurity.TransferReduction.checked_role_equation
set_option pp.all true in
#check @ShielddSecurity.TransferReduction.checked_inverse_nonzero
#print axioms ShielddSecurity.TransferReduction.checked_inverse_nonzero
