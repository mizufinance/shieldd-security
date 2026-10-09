import ShielddSecurity.ScalarRandomizerCompletion

set_option maxHeartbeats 400000

namespace ShielddSecurity.ScalarComparatorCompletion

variable {F : Type} [Field F]

def initialRows (value start width : Nat) : List Row :=
  (List.range' start width).map booleanRow ++
    [reconstructionRow value (List.range' start width)]

def constructedRows (value start width : Nat) (stages : List CompilerCompletion.Step) : List Row :=
  initialRows value start width ++ CompilerCompletion.emitted stages

def construct (base : Nat → F) (start width n : Nat)
    (stages : List CompilerCompletion.Step) : Nat → F :=
  CompilerCompletion.run (writeBits base start (encodeBits width n)) stages

/-- Construct the actual product recurrence for either comparison outcome.
The bound is an input to the Boolean comparison, not a promised endpoint.
Finite instances supply exact row/bit/write certificates independently. -/
theorem constructs {F : Type} [Field F] [CharP F Scalar.modulus]
    (base : Nat → F) (value start width n limit : Nat)
    (stages : List CompilerCompletion.Step) (kept : List Nat) (steps : List ScalarRows.StepData)
    (widthBound : n < 2^width) (capacity : 2^width < Scalar.modulus)
    (meaning : base value = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (ordered : CompilerCompletion.Topological kept (initialRows value start width) stages)
    (products : ScalarRandomizerCompletion.Products stages) (zeroKept : 0 ∈ kept) (valueKept : value ∈ kept)
    (outside : ∀ column ∈ kept, column < start ∨ start + width ≤ column)
    (bitOrder : steps.map ScalarRows.StepData.left =
      (List.range' start width).map (fun column => [(column, 1)]))
    (booleans : ScalarBits.checkBits Scalar.modulus (constructedRows value start width stages)
      (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain Scalar.modulus (constructedRows value start width stages)
      [(0, 1)] steps = true)
    (reconstruction : ScalarComparisonBounds.checkEquality Scalar.modulus
      (constructedRows value start width stages) (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left))
      [(value, 1)] = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = limit) :
    Satisfies (construct base start width n stages) (constructedRows value start width stages) ∧
      binary (ScalarBits.decodeBits (construct base start width n stages)
        (steps.map ScalarRows.StepData.left)) = n ∧
      eval (construct base start width n stages)
        (ScalarComparisonBounds.endpoint [(0, 1)] steps) = (if n ≤ limit then 1 else 0) ∧
      (∀ column ∈ kept, construct base start width n stages column = base column) := by
  let bitBase := writeBits base start (encodeBits width n)
  let rho := construct base start width n stages
  have initialized : Satisfies bitBase (initialRows value start width) :=
    writeBits_range_complete base value start width n widthBound meaning (outside value valueKept)
  have legal := ScalarRandomizerCompletion.products_legal bitBase stages products
  have completed : Satisfies rho (constructedRows value start width stages) :=
    CompilerCompletion.run_complete bitBase stages kept (initialRows value start width) ordered legal initialized
  have preserves (column : Nat) (member : column ∈ kept) : rho column = base column := by
    have result := CompilerCompletion.run_preserves bitBase stages kept
      (initialRows value start width) ordered column member
    exact result.trans (writeBits_preserves base start (encodeBits width n) column
      (by simpa only [encodeBits_length] using outside column member))
  have finalOne : rho 0 = 1 := (preserves 0 zeroKept).trans one
  have rebuilt := ScalarComparisonBounds.checked_equality rho
    (constructedRows value start width stages) completed _ [(value, 1)] reconstruction
  have decoded := ScalarBits.decoded_bits_value rho (constructedRows value start width stages)
    completed (steps.map ScalarRows.StepData.left) booleans
  have valueMeaning : eval rho [(value, 1)] = (n : F) := by
    simpa only [eval, Int.cast_one, one_mul, add_zero] using (preserves value valueKept).trans meaning
  have bitLength : (steps.map ScalarRows.StepData.left).length = width := by
    rw [bitOrder]
    simp only [List.length_map, List.length_range']
  have decodedBound : binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) <
      Scalar.modulus := by
    have bound := binary_bound (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left))
    simp only [ScalarBits.decodeBits, List.length_map, bitLength] at bound
    exact bound.trans capacity
  have integerMeaning : binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) = n :=
    bounded_cast_injective decodedBound (widthBound.trans capacity)
      (decoded.symm.trans (rebuilt.trans valueMeaning))
  have recurrence := ScalarRows.checked_chain_sound rho finalOne four
    (constructedRows value start width stages) completed [(0, 1)] steps chain
  rw [ScalarComparisonBounds.endpoint_value] at recurrence
  have initial : eval rho [(0, 1)] = 1 := by simp [eval, finalOne]
  rw [initial] at recurrence
  have comparison := ScalarBits.polynomial_chain_order rho (constructedRows value start width stages)
    completed steps booleans
  have sameInteger : binary (steps.map (fun step => ScalarBits.decodeBit rho step.left)) = n := by
    simpa only [ScalarBits.decodeBits, List.map_map] using integerMeaning
  rw [sameInteger, maximum] at comparison
  exact ⟨completed, integerMeaning, recurrence.trans comparison, preserves⟩

theorem bounded_endpoint {F : Type} [Field F] (rho : Nat → F)
    (steps : List ScalarRows.StepData) (n limit : Nat) (bound : n ≤ limit)
    (comparison : eval rho (ScalarComparisonBounds.endpoint [(0, 1)] steps) =
      (if n ≤ limit then 1 else 0)) :
    eval rho (ScalarComparisonBounds.endpoint [(0, 1)] steps) = 1 := by
  simpa only [if_pos bound] using comparison

set_option pp.all true in
#check @constructs
#print axioms constructs
set_option pp.all true in
#check @bounded_endpoint
#print axioms bounded_endpoint

end ShielddSecurity.ScalarComparatorCompletion
