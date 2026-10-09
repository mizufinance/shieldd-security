import ShielddSecurity.ScalarReductionSeed

set_option maxHeartbeats 300000

namespace ShielddSecurity.ScalarReductionAssertions

variable {F : Type} [Field F]

/-- The high bit is read from the actual four-bit write, after its column is
preserved. No quotient wire value or comparison outcome is supplied. -/
theorem quotient_high_value (base rho : Nat → F) (codec : TransferReduction.CanonicalField F)
    (value : F) (start : Nat)
    (preserved : rho (start+3) = writeBits base start
      (encodeBits 4 (ScalarReductionSeed.quotient codec value)) (start+3)) :
    eval rho [(start+3,1)] =
      (if ScalarReductionSeed.quotient codec value = 8 then 1 else 0) := by
  let q := ScalarReductionSeed.quotient codec value
  have qBound : q ≤ 8 := (ScalarReductionCompletion.decoded_operands codec value).1
  have qSmall : q < 2^4 := by omega
  have high : (encodeBits 4 q).getD 3 false = true ↔ q = 8 := by
    have result := ScalarReductionCompletion.quotient_high_iff_eight (encodeBits 4 q)
      (encodeBits_length 4 q) (by rw [encodeBits_value 4 q qSmall]; exact qBound)
    simpa only [encodeBits_value 4 q qSmall] using result
  have read : writeBits base start (encodeBits 4 q) (start+3) =
      (if (encodeBits 4 q).getD 3 false then (1 : F) else 0) := by
    simp only [writeBits,encodeBits_length]
    have inside : start ≤ start+3 ∧ start+3 < start+4 := by omega
    have position : start+3-start = 3 := by omega
    simp only [inside,if_true,position]
    rfl
  simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [preserved,read]
  change (if (encodeBits 4 q).getD 3 false then (1 : F) else 0) =
    (if q = 8 then 1 else 0)
  by_cases eight : q = 8
  · rw [high.mpr eight]
    simp only [if_pos eight,if_true]
  · have low : (encodeBits 4 q).getD 3 false = false := by
      cases bit : (encodeBits 4 q).getD 3 false with
      | false => rfl
      | true => exact False.elim (eight (high.mp bit))
    rw [low]
    simp only [if_neg eight,Bool.false_eq_true,if_false]

theorem terminal_endpoint {p : Nat} [CharP F p]
    (base rho : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F) (start : Nat)
    (rows : List Row) (steps : List ScalarRows.StepData)
    (satisfied : Satisfies rho rows) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (bitOrder : steps.map ScalarRows.StepData.left =
      (List.range' start 252).map (fun column => [(column,1)]))
    (preserved : ∀ column ∈ List.range' start 252,
      rho column = writeBits base start (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column)
    (booleans : ScalarBits.checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain p rows [(0,1)] steps = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.lastRemainder) :
    eval rho (ScalarComparisonBounds.endpoint [(0,1)] steps) =
      (if ScalarReductionSeed.remainder codec value ≤ Scalar.lastRemainder then 1 else 0) := by
  have bound : ScalarReductionSeed.remainder codec value < 2^252 :=
    (ScalarReductionCompletion.decoded_operands codec value).2.1.trans (by decide : Scalar.order < 2^252)
  have result := ScalarConstructedBits.comparison_from_written_bits base rho start
    (encodeBits 252 (ScalarReductionSeed.remainder codec value)) rows steps satisfied one four
    (by simpa only [encodeBits_length] using bitOrder)
    (by simpa only [encodeBits_length] using preserved) booleans chain
  simpa only [encodeBits_value 252 _ bound,maximum] using result.2

/-- The actual gate product rows supply multiplication, while the codec's
Euclidean last cap supplies its zero value. Satisfaction is used only for the
already constructed materializations, never assumed for the gate assertion. -/
theorem gate_zero {p : Nat} [CharP F p]
    (base rho : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qStart rStart : Nat) (rows : List Row) (steps : List ScalarRows.StepData)
    (satisfied : Satisfies rho rows) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (highPreserved : rho (qStart+3) = writeBits base qStart
      (encodeBits 4 (ScalarReductionSeed.quotient codec value)) (qStart+3))
    (bitOrder : steps.map ScalarRows.StepData.left =
      (List.range' rStart 252).map (fun column => [(column,1)]))
    (preserved : ∀ column ∈ List.range' rStart 252,
      rho column = writeBits base rStart (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column)
    (booleans : ScalarBits.checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain p rows [(0,1)] steps = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.lastRemainder)
    (gate : Linear) (product : ScalarRows.ProductData)
    (checkedProduct : ScalarRows.checkProduct p rows [(qStart+3,1)]
      (Compiler.subtract [(0,1)] (ScalarComparisonBounds.endpoint [(0,1)] steps)) gate product = true) :
    eval rho gate = 0 := by
  have high := quotient_high_value base rho codec value qStart highPreserved
  have terminal := terminal_endpoint base rho codec value rStart rows steps satisfied one four
    bitOrder preserved booleans chain maximum
  have multiplied := ScalarRows.checked_product_sound rho one four rows satisfied _ _ gate product checkedProduct
  rw [Compiler.eval_subtract,show eval rho [(0,1)] = 1 by simp [eval,one],high,terminal] at multiplied
  exact multiplied.trans (ScalarReductionCompletion.terminal_gate
    (ScalarReductionSeed.quotient codec value) (ScalarReductionSeed.remainder codec value)
    (ScalarReductionCompletion.decoded_operands codec value).2.2.1)

set_option pp.all true in
#check @quotient_high_value
#print axioms quotient_high_value
set_option pp.all true in
#check @terminal_endpoint
#print axioms terminal_endpoint
set_option pp.all true in
#check @gate_zero
#print axioms gate_zero

end ShielddSecurity.ScalarReductionAssertions
