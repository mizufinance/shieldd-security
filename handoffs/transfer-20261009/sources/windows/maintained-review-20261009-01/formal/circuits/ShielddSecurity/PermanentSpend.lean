import ShielddSecurity.SpendGateInputs

set_option maxHeartbeats 300000

namespace ShielddSecurity.PermanentSpend

variable {F : Type} [Field F]

/-- Subtraction by zero from the field's additive-group axioms alone. -/
theorem sub_zero_field (a : F) : a - 0 = a := by
  have negativeZero : -(0 : F) = 0 := by
    have cancelled : -(0 : F) + 0 = 0 := neg_add_cancel 0
    simpa only [add_zero] using cancelled
  rw [sub_eq_add_neg, negativeZero, add_zero]

/-- A vanishing difference gives equality using additive cancellation alone. -/
theorem eq_of_sub_zero_field (a b : F) (difference : a - b = 0) : a = b := by
  have cancelled := congrArg (fun z : F => z + b) difference
  simpa only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, zero_add] using cancelled


/-- Permanent spend selection, independent of hash and Merkle computation.
The dummy branch constrains its amount and synthetic nullifier; its computed
root is unrestricted by these gates. No history/window selector occurs here. -/
def BranchSpec (dummy amount nullifier realNullifier syntheticNullifier
    computedRoot anchor : F) : Prop :=
  (dummy = 0 ∧ nullifier = realNullifier ∧ computedRoot = anchor) ∨
  (dummy = 1 ∧ amount = 0 ∧ nullifier = syntheticNullifier)

/-- Every field assignment satisfying the optional-spend gates has one of the
two independent branch meanings. Bitness and each gate are explicit premises. -/
theorem branch_sound
    (dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor : F)
    (dummyBoolean : Square dummy dummy)
    (selected : nullifier = dummy * syntheticNullifier + (1 - dummy) * realNullifier)
    (anchorGate : (1 - dummy) * (computedRoot - anchor) = 0)
    (amountGate : dummy * amount = 0) :
    BranchSpec dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor := by
  rcases boolean_sound dummy dummyBoolean with zero | one
  · left
    refine ⟨zero, ?_, ?_⟩
    · simpa only [zero, zero_mul, sub_zero_field, one_mul, zero_add] using selected
    · exact eq_of_sub_zero_field _ _
        (by simpa only [zero, sub_zero_field, one_mul] using anchorGate)
  · right
    refine ⟨one, ?_, ?_⟩
    · simpa only [one, one_mul] using amountGate
    · simpa only [one, one_mul, sub_self, zero_mul, add_zero] using selected

/-- Completeness of these four gates only. This neither constructs compiler
auxiliaries nor asserts completeness of note hashes, range or Merkle rows. -/
theorem branch_gates_complete
    (dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor : F)
    (legal : BranchSpec dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor) :
    Square dummy dummy ∧
      nullifier = dummy * syntheticNullifier + (1 - dummy) * realNullifier ∧
      (1 - dummy) * (computedRoot - anchor) = 0 ∧ dummy * amount = 0 := by
  rcases legal with ⟨zero, real, root⟩ | ⟨one, empty, synthetic⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Square, zero, zero_mul]
    · simp only [zero, real, sub_zero_field, zero_mul, one_mul, zero_add]
    · simp only [zero, root, sub_zero_field, sub_self, one_mul]
    · simp only [zero, zero_mul]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Square, one, one_mul]
    · simp only [one, synthetic, one_mul, sub_self, zero_mul, add_zero]
    · simp only [one, sub_self, zero_mul]
    · simp only [one, empty, mul_zero]

/-- Explicit arbitrary-rho interface. Actual original rows and source LCs must
establish these gate premises before this theorem can be used for a circuit. -/
theorem assignment_branch_sound (rho : Nat → F)
    (dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor : Linear)
    (dummyBoolean : Square (eval rho dummy) (eval rho dummy))
    (selected : eval rho nullifier = eval rho dummy * eval rho syntheticNullifier +
      (1 - eval rho dummy) * eval rho realNullifier)
    (anchorGate : (1 - eval rho dummy) * (eval rho computedRoot - eval rho anchor) = 0)
    (amountGate : eval rho dummy * eval rho amount = 0) :
    BranchSpec (eval rho dummy) (eval rho amount) (eval rho nullifier)
      (eval rho realNullifier) (eval rho syntheticNullifier) (eval rho computedRoot) (eval rho anchor) :=
  branch_sound _ _ _ _ _ _ _ dummyBoolean selected anchorGate amountGate

/-- The required constructor uses direct real-nullifier/root assertions and
returns constant false. It needs neither an optional witness nor a history
premise; the fixed selector is an explicit constructor/source obligation. -/
theorem required_input_real
    (dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor : F)
    (constructorZero : dummy = 0)
    (nullifierGate : nullifier = realNullifier)
    (anchorGate : computedRoot = anchor) :
    dummy = 0 ∧ nullifier = realNullifier ∧ computedRoot = anchor ∧
      BranchSpec dummy amount nullifier realNullifier syntheticNullifier computedRoot anchor :=
  ⟨constructorZero, nullifierGate, anchorGate, Or.inl ⟨constructorZero, nullifierGate, anchorGate⟩⟩

theorem required_assignment_real (rho : Nat → F)
    (amount nullifier realNullifier syntheticNullifier computedRoot anchor : Linear)
    (nullifierGate : eval rho nullifier = eval rho realNullifier)
    (anchorGate : eval rho computedRoot = eval rho anchor) :
    eval rho [] = 0 ∧ eval rho nullifier = eval rho realNullifier ∧
      eval rho computedRoot = eval rho anchor ∧
      BranchSpec (eval rho []) (eval rho amount) (eval rho nullifier)
        (eval rho realNullifier) (eval rho syntheticNullifier) (eval rho computedRoot) (eval rho anchor) :=
  required_input_real _ _ _ _ _ _ _ (by rfl) nullifierGate anchorGate

set_option pp.all true in
#check @branch_sound
#print axioms branch_sound
set_option pp.all true in
#check @branch_gates_complete
#print axioms branch_gates_complete
set_option pp.all true in
#check @assignment_branch_sound
#print axioms assignment_branch_sound
set_option pp.all true in
#check @required_input_real
#print axioms required_input_real
set_option pp.all true in
#check @required_assignment_real
#print axioms required_assignment_real

end ShielddSecurity.PermanentSpend
