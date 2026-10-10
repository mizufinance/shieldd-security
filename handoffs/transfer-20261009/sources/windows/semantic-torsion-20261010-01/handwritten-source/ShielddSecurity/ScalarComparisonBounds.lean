import ShielddSecurity.ScalarBits

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ScalarComparisonBounds

variable {F : Type} [Field F]

/-- Original zero assertions may use either sign. This checks the actual row
orientation rather than claiming the two canonical LCs are equal. -/
def checkEquality (p : Nat) (rows : List Row) (left right : Linear) : Bool :=
  Compiler.checkRow p rows ⟨Compiler.subtract left right, []⟩ ||
    Compiler.checkRow p rows ⟨Compiler.subtract right left, []⟩

theorem checked_equality {p : Nat} [CharP F p] (rho : Nat → F)
    (rows : List Row) (satisfied : Satisfies rho rows) (left right : Linear)
    (checked : checkEquality p rows left right = true) : eval rho left = eval rho right := by
  simp only [checkEquality, Bool.or_eq_true] at checked
  rcases checked with forward | backward
  · exact Compiler.checked_assertion_sound rho rows left right satisfied forward
  · exact (Compiler.checked_assertion_sound rho rows right left satisfied backward).symm

def endpoint : Linear → List ScalarRows.StepData → Linear
  | initial, [] => initial
  | _, step :: tail => endpoint step.after tail

theorem endpoint_value (rho : Nat → F) (initial : Linear) (steps : List ScalarRows.StepData) :
    ScalarRows.evaluateChain rho initial steps = eval rho (endpoint initial steps) := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step tail ih => exact ih step.after

/-- Positive integer bound from arbitrary Boolean-constrained field wires and
the actual comparator recurrence/assertion rows. No desired integer bound,
canonical reduction, or native witness evaluator occurs in the premises. -/
theorem checked_comparison_bound {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows) (steps : List ScalarRows.StepData)
    (booleans : ScalarBits.checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain p rows [(0, 1)] steps = true)
    (ending : checkEquality p rows (endpoint [(0, 1)] steps) [(0, 1)] = true) :
    binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) ≤
      binary (steps.map ScalarRows.StepData.right) := by
  classical
  have recurrence := ScalarRows.checked_chain_sound rho one four rows satisfied [(0, 1)] steps chain
  have order := ScalarBits.polynomial_chain_order rho rows satisfied steps booleans
  have final := checked_equality rho rows satisfied (endpoint [(0, 1)] steps) [(0, 1)] ending
  rw [endpoint_value] at recurrence
  have initial : eval rho [(0, 1)] = 1 := by simp [eval, one]
  rw [initial] at recurrence final
  have truth := ScalarBits.field_condition_true
    (binary (steps.map (fun step => ScalarBits.decodeBit rho step.left)) ≤
      binary (steps.map ScalarRows.StepData.right))
    (order.symm.trans (recurrence.symm.trans final))
  simpa only [ScalarBits.decodeBits, List.map_map] using truth

/-- The maximum is the actual little-endian literal flag vector, a finite data
identity. r<ell is derived by comparison, not inferred from a field equality. -/
theorem checked_remainder_bound {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows) (steps : List ScalarRows.StepData)
    (booleans : ScalarBits.checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain p rows [(0, 1)] steps = true)
    (ending : checkEquality p rows (endpoint [(0, 1)] steps) [(0, 1)] = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.order - 1) :
    binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) < Scalar.order := by
  have bounded := checked_comparison_bound rho one four rows satisfied steps booleans chain ending
  rw [maximum] at bounded
  exact Nat.lt_of_le_of_lt bounded (by decide : Scalar.order - 1 < Scalar.order)

/-- The compiler materializes a product in a fresh output, then separately
asserts its target. Both original pieces are mandatory; output=target is not
substituted into the product rows as a premise. -/
theorem checked_terminal_product {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (left right output target : Linear) (data : ScalarRows.ProductData)
    (product : ScalarRows.checkProduct p rows left right output data = true)
    (assertion : checkEquality p rows output target = true) :
    eval rho left * eval rho right = eval rho target :=
  (ScalarRows.checked_product_sound rho one four rows satisfied left right output data product).symm.trans
    (checked_equality rho rows satisfied output target assertion)

/-- The unconditional last comparator is interpreted over the SAME decoded
remainder bits; its literal flags are p-1-8ell. At quotient eight the actual
high-bit * (1-lastWithin) product and assertion-zero force lastWithin=1.
The full actual last chain still needs a source/row certificate; first8 or32
recurrences cannot instantiate this theorem for all252 steps. -/
theorem checked_quotient_eight_cap {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (b0 b1 b2 high : Linear) (lastSteps : List ScalarRows.StepData)
    (qBooleans : ScalarBits.checkBits p rows [b0, b1, b2, high] = true)
    (rBooleans : ScalarBits.checkBits p rows (lastSteps.map ScalarRows.StepData.left) = true)
    (lastChain : ScalarRows.checkChain p rows [(0, 1)] lastSteps = true)
    (maximum : binary (lastSteps.map ScalarRows.StepData.right) = Scalar.lastRemainder)
    (output : Linear) (data : ScalarRows.ProductData)
    (product : ScalarRows.checkProduct p rows high
      ([(0, 1)] ++ scaleLinear (-1) (endpoint [(0, 1)] lastSteps)) output data = true)
    (assertion : checkEquality p rows output [] = true)
    (qEight : binary (ScalarBits.decodeBits rho [b0, b1, b2, high]) = 8) :
    binary (ScalarBits.decodeBits rho (lastSteps.map ScalarRows.StepData.left)) ≤ Scalar.lastRemainder := by
  classical
  have highFlag := ScalarBits.quotient_eight_high
    (ScalarBits.decodeBits rho [b0, b1, b2, high]) (by simp [ScalarBits.decodeBits]) qEight
  have highValue := ScalarBits.checked_bit_value rho rows satisfied [b0, b1, b2, high]
    qBooleans high (by simp)
  have highDecoded : ScalarBits.decodeBit rho high = true := by
    simpa [ScalarBits.decodeBits, List.getD] using highFlag
  rw [highDecoded] at highValue
  have guardValue := checked_terminal_product rho one four rows satisfied high
    ([(0, 1)] ++ scaleLinear (-1) (endpoint [(0, 1)] lastSteps)) output [] data product assertion
  have final : eval rho (endpoint [(0, 1)] lastSteps) = 1 := by
    have zero : 1 - eval rho (endpoint [(0, 1)] lastSteps) = 0 := by
      simpa [eval_append, eval_scale, eval, one, highValue, sub_eq_add_neg] using guardValue
    exact (sub_eq_zero.mp zero).symm
  have recurrence := ScalarRows.checked_chain_sound rho one four rows satisfied [(0, 1)] lastSteps lastChain
  rw [endpoint_value] at recurrence
  have initial : eval rho [(0, 1)] = 1 := by simp [eval, one]
  rw [initial] at recurrence
  have order := ScalarBits.polynomial_chain_order rho rows satisfied lastSteps rBooleans
  have bounded := ScalarBits.field_condition_true
    (binary (lastSteps.map (fun step => ScalarBits.decodeBit rho step.left)) ≤
      binary (lastSteps.map ScalarRows.StepData.right))
    (order.symm.trans (recurrence.symm.trans final))
  rw [maximum] at bounded
  simpa only [ScalarBits.decodeBits, List.map_map] using bounded

/-- Explicit no-wrap join: q≤8 and r<ell are INSUFFICIENT without the last
branch condition. These are interfaces to the row-derived lemmas above, not
an actual full-scalar theorem. CharP and both strict canonical bounds are
required for uniqueness of a separately supplied canonical representative. -/
theorem no_wrap_and_canonical {F : Type} [Field F] [CharP F Scalar.modulus]
    (hash : F) (q r canonicalValue : Nat)
    (qBound : q ≤ 8) (rBound : r < Scalar.order)
    (lastCap : q = 8 → r ≤ Scalar.lastRemainder)
    (equation : (q : F) * (Scalar.order : F) + (r : F) = hash)
    (canonicalBound : canonicalValue < Scalar.modulus)
    (canonicalMeaning : (canonicalValue : F) = hash) :
    q * Scalar.order + r < Scalar.modulus ∧
      canonicalValue = q * Scalar.order + r ∧ Scalar.Reduction canonicalValue q r := by
  have bounded := Scalar.reduction_sum_bound qBound rBound lastCap
  have meaning : ((q * Scalar.order + r : Nat) : F) = hash := by
    simpa only [Nat.cast_add, Nat.cast_mul] using equation
  have unique := Scalar.canonical_representative_unique hash canonicalValue
    (q * Scalar.order + r) canonicalBound bounded canonicalMeaning meaning
  exact ⟨bounded, unique, ⟨unique, rBound⟩⟩

/-- Complete symbolic scalar arithmetic join from checked Boolean, comparator,
assertion and equation rows. All three FULL chains and their same-wire/literal
certificates are premises; integer q/r bounds are conclusions. A caller's
canonical input is separately bounded below p, as required for cast injection.
This does not supply the still-pending actual252/508-row certificates, inverse,
source-DAG projection, or legal-input auxiliary completion. -/
theorem checked_canonical_reduction {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (qSteps rSteps lastSteps : List ScalarRows.StepData)
    (b0 b1 b2 high : Linear)
    (qBits : qSteps.map ScalarRows.StepData.left = [b0, b1, b2, high])
    (sameRBits : lastSteps.map ScalarRows.StepData.left = rSteps.map ScalarRows.StepData.left)
    (qBoolean : ScalarBits.checkBits Scalar.modulus rows (qSteps.map ScalarRows.StepData.left) = true)
    (rBoolean : ScalarBits.checkBits Scalar.modulus rows (rSteps.map ScalarRows.StepData.left) = true)
    (qChain : ScalarRows.checkChain Scalar.modulus rows [(0, 1)] qSteps = true)
    (rChain : ScalarRows.checkChain Scalar.modulus rows [(0, 1)] rSteps = true)
    (lastChain : ScalarRows.checkChain Scalar.modulus rows [(0, 1)] lastSteps = true)
    (qEnd : checkEquality Scalar.modulus rows (endpoint [(0, 1)] qSteps) [(0, 1)] = true)
    (rEnd : checkEquality Scalar.modulus rows (endpoint [(0, 1)] rSteps) [(0, 1)] = true)
    (qMaximum : binary (qSteps.map ScalarRows.StepData.right) = 8)
    (rMaximum : binary (rSteps.map ScalarRows.StepData.right) = Scalar.order - 1)
    (lastMaximum : binary (lastSteps.map ScalarRows.StepData.right) = Scalar.lastRemainder)
    (output hash : Linear) (data : ScalarRows.ProductData)
    (guardProduct : ScalarRows.checkProduct Scalar.modulus rows high
      ([(0, 1)] ++ scaleLinear (-1) (endpoint [(0, 1)] lastSteps)) output data = true)
    (guardAssertion : checkEquality Scalar.modulus rows output [] = true)
    (equation : checkEquality Scalar.modulus rows
      (scaleLinear (Scalar.order : Int) (ScalarBits.bitLinear (qSteps.map ScalarRows.StepData.left)) ++
        ScalarBits.bitLinear (rSteps.map ScalarRows.StepData.left)) hash = true)
    (canonicalValue : Nat) (canonicalBound : canonicalValue < Scalar.modulus)
    (canonicalMeaning : (canonicalValue : F) = eval rho hash) :
    let q := binary (ScalarBits.decodeBits rho (qSteps.map ScalarRows.StepData.left))
    let r := binary (ScalarBits.decodeBits rho (rSteps.map ScalarRows.StepData.left))
    q ≤ 8 ∧ r < Scalar.order ∧ (q = 8 → r ≤ Scalar.lastRemainder) ∧
      q * Scalar.order + r < Scalar.modulus ∧ Scalar.Reduction canonicalValue q r := by
  classical
  let q := binary (ScalarBits.decodeBits rho (qSteps.map ScalarRows.StepData.left))
  let r := binary (ScalarBits.decodeBits rho (rSteps.map ScalarRows.StepData.left))
  have qBound : q ≤ 8 := by
    have bound := checked_comparison_bound rho one four rows satisfied qSteps qBoolean qChain qEnd
    simpa only [qMaximum] using bound
  have rBound : r < Scalar.order :=
    checked_remainder_bound rho one four rows satisfied rSteps rBoolean rChain rEnd rMaximum
  have lastCap : q = 8 → r ≤ Scalar.lastRemainder := by
    intro qEight
    have qChecks : ScalarBits.checkBits Scalar.modulus rows [b0, b1, b2, high] = true := by
      simpa only [qBits] using qBoolean
    have rChecks : ScalarBits.checkBits Scalar.modulus rows (lastSteps.map ScalarRows.StepData.left) = true := by
      simpa only [sameRBits] using rBoolean
    have last := checked_quotient_eight_cap rho one four rows satisfied b0 b1 b2 high lastSteps
      qChecks rChecks lastChain lastMaximum output data guardProduct guardAssertion
      (by simpa only [q, qBits] using qEight)
    simpa only [sameRBits] using last
  have qValue := ScalarBits.decoded_bits_value rho rows satisfied
    (qSteps.map ScalarRows.StepData.left) qBoolean
  have rValue := ScalarBits.decoded_bits_value rho rows satisfied
    (rSteps.map ScalarRows.StepData.left) rBoolean
  have fieldEquation : (q : F) * (Scalar.order : F) + (r : F) = eval rho hash := by
    have checked := checked_equality rho rows satisfied _ hash equation
    simpa only [q, r, eval_append, eval_scale, Int.cast_ofNat, Int.cast_natCast, qValue, rValue, mul_comm] using checked
  have joined := no_wrap_and_canonical (eval rho hash) q r canonicalValue qBound rBound lastCap
    fieldEquation canonicalBound canonicalMeaning
  exact ⟨qBound, rBound, lastCap, joined.1, joined.2.2⟩


end ShielddSecurity.ScalarComparisonBounds

set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checkEquality
#print axioms ShielddSecurity.ScalarComparisonBounds.checkEquality
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checked_equality
#print axioms ShielddSecurity.ScalarComparisonBounds.checked_equality
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.endpoint
#print axioms ShielddSecurity.ScalarComparisonBounds.endpoint
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.endpoint_value
#print axioms ShielddSecurity.ScalarComparisonBounds.endpoint_value
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checked_comparison_bound
#print axioms ShielddSecurity.ScalarComparisonBounds.checked_comparison_bound
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checked_remainder_bound
#print axioms ShielddSecurity.ScalarComparisonBounds.checked_remainder_bound
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checked_terminal_product
#print axioms ShielddSecurity.ScalarComparisonBounds.checked_terminal_product
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checked_quotient_eight_cap
#print axioms ShielddSecurity.ScalarComparisonBounds.checked_quotient_eight_cap
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.no_wrap_and_canonical
#print axioms ShielddSecurity.ScalarComparisonBounds.no_wrap_and_canonical
set_option pp.all true in
#check @ShielddSecurity.ScalarComparisonBounds.checked_canonical_reduction
#print axioms ShielddSecurity.ScalarComparisonBounds.checked_canonical_reduction
