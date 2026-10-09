import ShielddSecurity.ScalarRows

set_option maxHeartbeats 500000

namespace ShielddSecurity.ScalarBits

variable {F : Type} [Field F]

noncomputable def decodeBit (rho : Nat → F) (bit : Linear) : Bool := by
  classical
  exact decide (eval rho bit = 1)

noncomputable def decodeBits (rho : Nat → F) (bits : List Linear) : List Bool :=
  bits.map (decodeBit rho)

def checkBits (p : Nat) (rows : List Row) (bits : List Linear) : Bool :=
  bits.all (fun bit => Compiler.checkRow p rows ⟨bit, bit⟩)

theorem decoded_bit_value (rho : Nat → F) (bit : Linear)
    (row : Square (eval rho bit) (eval rho bit)) :
    eval rho bit = (if decodeBit rho bit then 1 else 0) := by
  classical
  rcases boolean_sound (eval rho bit) row with zero | one
  · simp [decodeBit, zero]
  · simp [decodeBit, one]

theorem checked_bit_value {p : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (satisfied : Satisfies rho rows)
    (bits : List Linear) (checked : checkBits p rows bits = true)
    (bit : Linear) (member : bit ∈ bits) :
    eval rho bit = (if decodeBit rho bit then 1 else 0) := by
  apply decoded_bit_value rho bit
  exact Compiler.checked_row_sound rho rows ⟨bit, bit⟩ satisfied
    ((List.all_eq_true.mp checked) bit member)

def bitLinear : List Linear → Linear
  | [] => []
  | bit :: tail => bit ++ scaleLinear 2 (bitLinear tail)

theorem eval_bitLinear (rho : Nat → F) (bits : List Linear) :
    eval rho (bitLinear bits) = fieldBinary (bits.map (eval rho)) := by
  induction bits with
  | nil => rfl
  | cons bit tail ih =>
      simp only [bitLinear, eval_append, eval_scale, Int.cast_ofNat,
        List.map_cons, fieldBinary, ih]

theorem decoded_bits_value {p : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (satisfied : Satisfies rho rows)
    (bits : List Linear) (checked : checkBits p rows bits = true) :
    eval rho (bitLinear bits) = (binary (decodeBits rho bits) : F) := by
  classical
  have mapValue : bits.map (eval rho) =
      (decodeBits rho bits).map (fun bit => if bit then (1 : F) else 0) := by
    simp only [decodeBits, List.map_map]
    apply List.map_congr_left
    intro bit member
    exact checked_bit_value rho rows satisfied bits checked bit member
  rw [eval_bitLinear, mapValue, binary_cast]

/-- Integer meaning is constructed from arbitrary constrained bits. Neither a
native quotient nor its range is supplied as a semantic premise. -/
theorem checked_reconstruction {p : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (satisfied : Satisfies rho rows)
    (bits : List Linear) (value : Linear)
    (checked : checkBits p rows bits = true)
    (reconstruction : Compiler.checkRow p rows
      ⟨Compiler.subtract (bitLinear bits) value, []⟩ = true) :
    binary (decodeBits rho bits) < 2 ^ bits.length ∧
      (binary (decodeBits rho bits) : F) = eval rho value := by
  constructor
  · simpa only [decodeBits, List.length_map] using binary_bound (decodeBits rho bits)
  · have integer := decoded_bits_value rho rows satisfied bits checked
    have boundary := Compiler.checked_assertion_sound rho rows (bitLinear bits) value
      satisfied reconstruction
    exact integer.symm.trans boundary

/-- Little-endian comparison: later, more significant bits override the lower
prefix when unequal. The Boolean seed decides only an exact integer tie. -/
def comparisonFold : Bool → List Bool → List Bool → Bool
  | lower, [], [] => lower
  | lower, left :: ls, right :: rs =>
      comparisonFold (Scalar.comparisonStep lower left right) ls rs
  | _, _, _ => false

theorem comparison_fold_order (left right : List Bool)
    (sameLength : left.length = right.length) (lower : Bool) :
    comparisonFold lower left right = true ↔
      binary left < binary right ∨ (binary left = binary right ∧ lower = true) := by
  induction left generalizing right lower with
  | nil =>
      cases right with
      | nil => simp [comparisonFold, binary]
      | cons right tail => simp at sameLength
  | cons left tail ih =>
      cases right with
      | nil => simp at sameLength
      | cons right rest =>
          have lengths : tail.length = rest.length := Nat.succ.inj sameLength
          rw [comparisonFold, ih rest lengths]
          cases left <;> cases right <;> cases lower <;>
            simp [binary, Scalar.comparisonStep] <;> omega

theorem comparison_fold_le (left right : List Bool)
    (sameLength : left.length = right.length) :
    comparisonFold true left right = true ↔ binary left ≤ binary right := by
  rw [comparison_fold_order left right sameLength]
  simp only [and_true]
  omega

/-- Row-proved Boolean values turn the field recurrence into the independent
integer comparator. This induction is over a list, not a wide constraint walk. -/
theorem polynomial_chain_decoded {p : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (satisfied : Satisfies rho rows)
    (steps : List ScalarRows.StepData)
    (checked : checkBits p rows (steps.map ScalarRows.StepData.left) = true)
    (lower : Bool) :
    ScalarRows.polynomialChain rho (if lower then 1 else 0) steps =
      (if comparisonFold lower (steps.map (fun step => decodeBit rho step.left))
        (steps.map ScalarRows.StepData.right) then 1 else 0) := by
  induction steps generalizing lower with
  | nil => rfl
  | cons step tail ih =>
      have bit := checked_bit_value rho rows satisfied
        ((step :: tail).map ScalarRows.StepData.left) checked step.left (by simp)
      have tailChecked : checkBits p rows (tail.map ScalarRows.StepData.left) = true := by
        have all := checked
        simp only [checkBits, List.map_cons, List.all_cons, Bool.and_eq_true] at all
        exact all.2
      simp only [ScalarRows.polynomialChain, List.map_cons, comparisonFold]
      rw [bit, Scalar.comparison_polynomial_correct]
      exact ih tailChecked (Scalar.comparisonStep lower (decodeBit rho step.left) step.right)

theorem polynomial_chain_order {p : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (satisfied : Satisfies rho rows)
    (steps : List ScalarRows.StepData)
    (checked : checkBits p rows (steps.map ScalarRows.StepData.left) = true) :
    ScalarRows.polynomialChain rho 1 steps =
      (if binary (steps.map (fun step => decodeBit rho step.left)) ≤
        binary (steps.map ScalarRows.StepData.right) then 1 else 0) := by
  have decoded := polynomial_chain_decoded rho rows satisfied steps checked true
  have lengths : (steps.map (fun step => decodeBit rho step.left)).length =
      (steps.map ScalarRows.StepData.right).length := by simp only [List.length_map]
  have order := comparison_fold_le
    (steps.map (fun step => decodeBit rho step.left))
    (steps.map ScalarRows.StepData.right) lengths
  cases result : comparisonFold true (steps.map (fun step => decodeBit rho step.left))
      (steps.map ScalarRows.StepData.right) <;> simp_all

theorem field_condition_true (condition : Prop) [Decidable condition]
    (result : (if condition then (1 : F) else 0) = 1) : condition := by
  by_contra falseCondition
  simp [falseCondition] at result

/-- The four actual quotient bits encode eight only when bit three is one.
This bounded lemma supplies the final-short-interval guard; it does not assume
that the quotient witness is honestly reduced. -/
theorem quotient_eight_high (bits : List Bool) (width : bits.length = 4)
    (value : binary bits = 8) : bits.getD 3 false = true := by
  cases bits with
  | nil => simp at width
  | cons b0 tail0 =>
      cases tail0 with
      | nil => simp at width
      | cons b1 tail1 =>
          cases tail1 with
          | nil => simp at width
          | cons b2 tail2 =>
              cases tail2 with
              | nil => simp at width
              | cons b3 tail3 =>
                  cases tail3 with
                  | cons b4 tail4 => simp at width
                  | nil =>
                      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
                        simp [binary, List.getD] at value ⊢

#print axioms decoded_bit_value
#print axioms checked_bit_value
#print axioms decoded_bits_value
#print axioms checked_reconstruction
#print axioms comparison_fold_order
#print axioms comparison_fold_le
#print axioms polynomial_chain_decoded
#print axioms polynomial_chain_order
#print axioms field_condition_true
#print axioms quotient_eight_high

end ShielddSecurity.ScalarBits
