import ShielddSecurity.ScalarComparisonBounds

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferCanonicalBalance
open ScalarComparisonBounds

/-- Arbitrary satisfying assignments give a canonical scalar in the actual
committed column only after both decomposition and private/committed equality
rows check. Comparator recurrence checks are explicit executable premises;
no honest evaluator or desired scalar bound is assumed. -/
theorem checked_committed_canonical {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (steps : List ScalarRows.StepData) (privateValue : Linear)
    (booleans : ScalarBits.checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain p rows [(0, 1)] steps = true)
    (ending : checkEquality p rows (endpoint [(0, 1)] steps) [(0, 1)] = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.order - 1)
    (reconstruction : checkEquality p rows
      (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) privateValue = true)
    (committedLink : checkEquality p rows privateValue [(2, 1)] = true) :
    ∃ n : Nat, n < Scalar.order ∧ (n : F) = rho 2 := by
  let n := binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left))
  have bounded : n < Scalar.order := checked_remainder_bound rho one four rows satisfied
    steps booleans chain ending maximum
  have decoded := ScalarBits.decoded_bits_value rho rows satisfied
    (steps.map ScalarRows.StepData.left) booleans
  have rebuilt := checked_equality rho rows satisfied
    (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) privateValue reconstruction
  have linked := checked_equality rho rows satisfied privateValue [(2, 1)] committedLink
  refine ⟨n, bounded, ?_⟩
  simpa [n, eval] using decoded.symm.trans (rebuilt.trans linked)

set_option pp.all true in
#check @checked_committed_canonical
#print axioms checked_committed_canonical

end ShielddSecurity.TransferCanonicalBalance
