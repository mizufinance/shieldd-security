import ShielddSecurity.TransferReduction

set_option maxHeartbeats 300000

namespace ShielddSecurity.FieldEncoding

theorem binary_parity (bits : List Bool) :
    binary bits % 2 = if bits.getD 0 false then 1 else 0 := by
  cases bits with
  | nil => rfl
  | cons bit tail =>
      cases bit <;> simp [binary, List.getD, Nat.add_mod]

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- The literal maximum and actual comparator/assertion certificates supply
the field bound. No canonical witness value or desired bound is a premise. -/
theorem checked_encoding (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (steps : List ScalarRows.StepData) (value : Linear)
    (bits : ScalarBits.checkBits Scalar.modulus rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain Scalar.modulus rows [(0, 1)] steps = true)
    (ending : ScalarComparisonBounds.checkEquality Scalar.modulus rows
      (ScalarComparisonBounds.endpoint [(0, 1)] steps) [(0, 1)] = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.modulus - 1)
    (rebuild : ScalarComparisonBounds.checkEquality Scalar.modulus rows
      (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) value = true) :
    codec.decode (eval rho value) =
      binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) := by
  have bounded := ScalarComparisonBounds.checked_comparison_bound rho one four
    rows satisfied steps bits chain ending
  rw [maximum] at bounded
  have small : binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) <
      Scalar.modulus := Nat.lt_of_le_of_lt bounded (by decide)
  have decoded := ScalarBits.decoded_bits_value rho rows satisfied
    (steps.map ScalarRows.StepData.left) bits
  have reconstructed := ScalarComparisonBounds.checked_equality rho rows satisfied
    (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) value rebuild
  rw [← reconstructed, decoded]
  exact TransferReduction.decode_canonical_cast codec _ small

/-- Same-row parity linkage binds the selected root's sign to the actual choice
wire. A native byte encoder must separately satisfy its global byte contract. -/
theorem checked_parity (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (first : ScalarRows.StepData) (tail : List ScalarRows.StepData)
    (value choice : Linear)
    (bits : ScalarBits.checkBits Scalar.modulus rows
      ((first :: tail).map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain Scalar.modulus rows [(0, 1)] (first :: tail) = true)
    (ending : ScalarComparisonBounds.checkEquality Scalar.modulus rows
      (ScalarComparisonBounds.endpoint [(0, 1)] (first :: tail)) [(0, 1)] = true)
    (maximum : binary ((first :: tail).map ScalarRows.StepData.right) = Scalar.modulus - 1)
    (rebuild : ScalarComparisonBounds.checkEquality Scalar.modulus rows
      (ScalarBits.bitLinear ((first :: tail).map ScalarRows.StepData.left)) value = true)
    (parity : ScalarComparisonBounds.checkEquality Scalar.modulus rows first.left choice = true) :
    codec.decode (eval rho value) % 2 = if ScalarBits.decodeBit rho choice then 1 else 0 := by
  classical
  rw [checked_encoding codec rho one four rows satisfied (first :: tail) value
    bits chain ending maximum rebuild, binary_parity]
  have same := ScalarComparisonBounds.checked_equality rho rows satisfied first.left choice parity
  change (if ScalarBits.decodeBit rho first.left then 1 else 0) =
    (if ScalarBits.decodeBit rho choice then 1 else 0)
  simp only [ScalarBits.decodeBit, same]
  rfl

set_option pp.all true in
#check @binary_parity
#print axioms binary_parity
set_option pp.all true in
#check @checked_encoding
#print axioms checked_encoding
set_option pp.all true in
#check @checked_parity
#print axioms checked_parity

end ShielddSecurity.FieldEncoding
