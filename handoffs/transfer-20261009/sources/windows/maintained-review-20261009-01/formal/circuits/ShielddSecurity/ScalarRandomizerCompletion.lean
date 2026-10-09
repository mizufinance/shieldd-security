import ShielddSecurity.CompilerCompletion
import ShielddSecurity.ScalarComparisonBounds

set_option maxHeartbeats 500000

namespace ShielddSecurity.ScalarRandomizerCompletion

variable {F : Type} [Field F]

/-- This predicate admits only owned product materializations. In particular,
it excludes equality stages whose legality could assume the desired endpoint. -/
def Products : List CompilerCompletion.Step → Prop
  | [] => True
  | .product _ _ _ _ _ :: tail => Products tail
  | _ :: _ => False

theorem products_legal (base : Nat → F) (stages : List CompilerCompletion.Step)
    (products : Products stages) : CompilerCompletion.Legal base stages := by
  induction stages generalizing base with
  | nil => trivial
  | cons stage tail ih =>
      cases stage with
      | square input remainder output => cases products
      | product left right remainder output auxiliary => exact ⟨True.intro, ih _ products⟩
      | equal left right => cases products
      | squareEqual input target => cases products

/-- Compose bounded certificates without deciding a wide compiler-stage walk. -/
theorem ordered_append (kept : List Nat) (prior : List Row)
    (front back : List CompilerCompletion.Step)
    (first : CompilerCompletion.Topological kept prior front)
    (second : CompilerCompletion.Topological kept
      (prior ++ CompilerCompletion.emitted front) back) :
    CompilerCompletion.Topological kept prior (front ++ back) := by
  induction front generalizing prior with
  | nil => simpa only [CompilerCompletion.emitted, List.append_nil] using second
  | cons stage tail ih =>
      change stage.Shape ∧ _ ∧ _ ∧ _
      refine ⟨first.1, first.2.1, first.2.2.1, ?_⟩
      apply ih (prior ++ stage.rows) first.2.2.2
      simpa only [CompilerCompletion.emitted, List.append_assoc] using second

theorem products_append (front back : List CompilerCompletion.Step)
    (first : Products front) (second : Products back) : Products (front ++ back) := by
  induction front with
  | nil => exact second
  | cons stage tail ih =>
      cases stage with
      | square input remainder output => cases first
      | product left right remainder output auxiliary => exact ih first
      | equal left right => cases first
      | squareEqual input target => cases first

def initialRows (value start : Nat) : List Row :=
  (List.range' start 252).map booleanRow ++
    [reconstructionRow value (List.range' start 252)]

def constructedRows (value start : Nat) (stages : List CompilerCompletion.Step) : List Row :=
  initialRows value start ++ CompilerCompletion.emitted stages

def construct (base : Nat → F) (start n : Nat)
    (stages : List CompilerCompletion.Step) : Nat → F :=
  CompilerCompletion.run (writeBits base start (encodeBits 252 n)) stages

/-- Build the captured bit block and every owned comparator product. A strict
canonical input bound derives the endpoint; no row satisfaction, comparator
result, desired scalar multiplication, or subgroup premise is supplied.
The checker/ownership premises are exact finite instance certificates. -/
theorem constructs {F : Type} [Field F] [CharP F Scalar.modulus]
    (base : Nat → F) (value start n : Nat) (stages : List CompilerCompletion.Step)
    (kept : List Nat) (steps : List ScalarRows.StepData)
    (canonical : n < Scalar.order) (meaning : base value = (n : F))
    (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (ordered : CompilerCompletion.Topological kept (initialRows value start) stages)
    (products : Products stages) (zeroKept : 0 ∈ kept) (valueKept : value ∈ kept)
    (outside : ∀ column ∈ kept, column < start ∨ start + 252 ≤ column)
    (bitOrder : steps.map ScalarRows.StepData.left =
      (List.range' start 252).map (fun column => [(column, 1)]))
    (booleans : ScalarBits.checkBits Scalar.modulus (constructedRows value start stages)
      (steps.map ScalarRows.StepData.left) = true)
    (chain : ScalarRows.checkChain Scalar.modulus (constructedRows value start stages)
      [(0, 1)] steps = true)
    (reconstruction : ScalarComparisonBounds.checkEquality Scalar.modulus
      (constructedRows value start stages) (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left))
      [(value, 1)] = true)
    (maximum : binary (steps.map ScalarRows.StepData.right) = Scalar.order - 1) :
    Satisfies (construct base start n stages) (constructedRows value start stages) ∧
      binary (ScalarBits.decodeBits (construct base start n stages)
        (steps.map ScalarRows.StepData.left)) = n ∧
      eval (construct base start n stages)
        (ScalarComparisonBounds.endpoint [(0, 1)] steps) = 1 ∧
      (∀ column ∈ kept, construct base start n stages column = base column) := by
  let bitBase := writeBits base start (encodeBits 252 n)
  let rho := construct base start n stages
  have widthBound : n < 2^252 :=
    Nat.lt_trans canonical (by decide : Scalar.order < 2^252)
  have initialized : Satisfies bitBase (initialRows value start) :=
    writeBits_range_complete base value start 252 n widthBound meaning (outside value valueKept)
  have legal := products_legal bitBase stages products
  have completed : Satisfies rho (constructedRows value start stages) :=
    CompilerCompletion.run_complete bitBase stages kept (initialRows value start) ordered legal initialized
  have preserves (column : Nat) (member : column ∈ kept) : rho column = base column := by
    have result := CompilerCompletion.run_preserves bitBase stages kept
      (initialRows value start) ordered column member
    exact result.trans (writeBits_preserves base start (encodeBits 252 n) column
      (by simpa only [encodeBits_length] using outside column member))
  have finalOne : rho 0 = 1 := (preserves 0 zeroKept).trans one
  have reconstructed := ScalarComparisonBounds.checked_equality rho
    (constructedRows value start stages) completed _ [(value, 1)] reconstruction
  have decoded := ScalarBits.decoded_bits_value rho (constructedRows value start stages)
    completed (steps.map ScalarRows.StepData.left) booleans
  have valueMeaning : eval rho [(value, 1)] = (n : F) := by
    simpa only [eval, Int.cast_one, one_mul, add_zero] using
      (preserves value valueKept).trans meaning
  have lengthBits : (steps.map ScalarRows.StepData.left).length = 252 := by
    rw [bitOrder]
    simp only [List.length_map, List.length_range']
  have decodedBound : binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) <
      Scalar.modulus := by
    have bound := binary_bound (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left))
    simp only [ScalarBits.decodeBits, List.length_map, lengthBits] at bound
    exact Nat.lt_trans bound (by decide : 2^252 < Scalar.modulus)
  have integerMeaning : binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) = n :=
    bounded_cast_injective decodedBound
      (Nat.lt_trans canonical (by decide : Scalar.order < Scalar.modulus))
      (decoded.symm.trans (reconstructed.trans valueMeaning))
  have recurrence := ScalarRows.checked_chain_sound rho finalOne four
    (constructedRows value start stages) completed [(0, 1)] steps chain
  rw [ScalarComparisonBounds.endpoint_value] at recurrence
  have initial : eval rho [(0, 1)] = 1 := by simp [eval, finalOne]
  rw [initial] at recurrence
  have comparison := ScalarBits.polynomial_chain_order rho (constructedRows value start stages)
    completed steps booleans
  have lower : binary (steps.map (fun step => ScalarBits.decodeBit rho step.left)) ≤
      binary (steps.map ScalarRows.StepData.right) := by
    have value : binary (steps.map (fun step => ScalarBits.decodeBit rho step.left)) = n := by
      simpa only [ScalarBits.decodeBits, List.map_map] using integerMeaning
    rw [value, maximum]
    omega
  rw [if_pos lower] at comparison
  exact ⟨completed, integerMeaning, recurrence.trans comparison, preserves⟩

set_option pp.all true in
#check @products_legal
#print axioms products_legal
set_option pp.all true in
#check @ordered_append
#print axioms ordered_append
set_option pp.all true in
#check @products_append
#print axioms products_append
set_option pp.all true in
#check @constructs
#print axioms constructs

end ShielddSecurity.ScalarRandomizerCompletion
