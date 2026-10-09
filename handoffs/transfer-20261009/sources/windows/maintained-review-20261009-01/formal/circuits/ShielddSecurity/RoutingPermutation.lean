import ShielddSecurity.ScalarComparisonBounds

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.RoutingPermutation

/-- The actual 255-bit reconstruction is interpreted together with its
modulus-minus-one comparator. It never uses 2^255 < modulus. -/
theorem canonical_sound {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (rows : List Row) (steps : List ScalarRows.StepData)
    (output : Linear) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows)
    (booleans : ScalarBits.checkBits Scalar.modulus rows
      (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain Scalar.modulus rows [(0,1)] steps = true)
    (ending : ScalarComparisonBounds.checkEquality Scalar.modulus rows
      (ScalarComparisonBounds.endpoint [(0,1)] steps) [(0,1)] = true)
    (reconstruction : ScalarComparisonBounds.checkEquality Scalar.modulus rows
      (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) output = true)
    (width : steps.length = 255)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.modulus - 1) :
    let decoded := binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left))
    decoded < Scalar.modulus ∧ (decoded : F) = eval rho output := by
  have bound := ScalarComparisonBounds.checked_comparison_bound rho one four
    rows satisfied steps booleans chain ending
  rw [maximum] at bound
  have strict : binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) <
      Scalar.modulus := bound.trans_lt (by decide : Scalar.modulus - 1 < Scalar.modulus)
  have values := ScalarBits.decoded_bits_value rho rows satisfied
    (steps.map ScalarRows.StepData.left) booleans
  have equation := ScalarComparisonBounds.checked_equality rho rows satisfied
    (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) output reconstruction
  exact ⟨strict, values.symm.trans equation⟩

/-- A native canonical field reader on the same actual hash output identifies
the decoded integer. Its field reading contract is global, not desired bits. -/
theorem native_integer {F : Type} [Field F] [CharP F Scalar.modulus]
    (decoded native : Nat) (output : F)
    (decodedBound : decoded < Scalar.modulus) (nativeBound : native < Scalar.modulus)
    (reconstructed : (decoded : F) = output) (reader : (native : F) = output) :
    decoded = native :=
  bounded_cast_injective decodedBound nativeBound (reconstructed.trans reader.symm)

set_option pp.all true in
#check @canonical_sound
#print axioms canonical_sound
set_option pp.all true in
#check @native_integer
#print axioms native_integer

end ShielddSecurity.RoutingPermutation
