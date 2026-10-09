import ShielddSecurity.Volume

set_option maxHeartbeats 300000

namespace ShielddSecurity.Spend

variable {F : Type} [Field F]

/-- Local spend selection contract, independently of the compiled gate encoding.
The real/synthetic nullifiers and computed root are inputs to this slice. Their
hash/Merkle meanings and the public binding of `anchor` are separate obligations. -/
def BranchSpec (dummy history amount nullifier realNullifier syntheticNullifier
    computedRoot anchor : F) (position recentFloor : Nat) : Prop :=
  (dummy = 0 ∧ nullifier = realNullifier ∧ computedRoot = anchor ∧
    history = (if position < recentFloor then 1 else 0)) ∨
  (dummy = 1 ∧ amount = 0 ∧ nullifier = syntheticNullifier ∧ history = 0)

/-- Algebraic gate consequences, quantified over arbitrary field assignments.
`oldCorrect` must be discharged from the actual bounded comparison rows; it is
not a witness-generator guarantee. This theorem alone is not a runtime result. -/
theorem branch_sound
    (dummy history amount nullifier realNullifier syntheticNullifier computedRoot anchor old : F)
    (position recentFloor : Nat)
    (dummyBoolean : Square dummy dummy)
    (selected : nullifier = dummy * syntheticNullifier + (1 - dummy) * realNullifier)
    (anchorGate : (1 - dummy) * (computedRoot - anchor) = 0)
    (amountGate : dummy * amount = 0)
    (historyGate : history = (1 - dummy) * old)
    (oldCorrect : old = (if position < recentFloor then 1 else 0)) :
    BranchSpec dummy history amount nullifier realNullifier syntheticNullifier
      computedRoot anchor position recentFloor := by
  rcases boolean_sound dummy dummyBoolean with hd | hd
  · left
    refine ⟨hd, ?_, ?_, ?_⟩
    · simpa [hd] using selected
    · apply sub_eq_zero.mp
      simpa [hd] using anchorGate
    · simpa [hd, oldCorrect] using historyGate
  · right
    refine ⟨hd, ?_, ?_, ?_⟩
    · simpa [hd] using amountGate
    · simpa [hd] using selected
    · simpa [hd] using historyGate

/-- Every legal branch satisfies the algebraic gates. Compiled auxiliary-row
extension is a separate theorem, not supplied by this implication. -/
theorem branch_gates_complete
    (dummy history amount nullifier realNullifier syntheticNullifier computedRoot anchor : F)
    (position recentFloor : Nat)
    (legal : BranchSpec dummy history amount nullifier realNullifier syntheticNullifier
      computedRoot anchor position recentFloor) :
    Square dummy dummy ∧
    nullifier = dummy * syntheticNullifier + (1 - dummy) * realNullifier ∧
    (1 - dummy) * (computedRoot - anchor) = 0 ∧
    dummy * amount = 0 ∧
    history = (1 - dummy) * (if position < recentFloor then 1 else 0) := by
  rcases legal with ⟨hd, hn, ha, hh⟩ | ⟨hd, hm, hn, hh⟩
  · simp [Square, hd, hn, ha, hh]
  · simp [Square, hd, hm, hn, hh]

/-- The history selector is the borrow of `position - recentFloor`. Both
integers and the difference must be bounded, even for dummy inputs. In
particular equality with the floor is recent. No honest-witness assumption
or unrestricted field-to-integer conversion is used. -/
theorem history_comparison_sound {p bound position recentFloor difference : Nat}
    [CharP F p] (old : F)
    (capacity : 2 * bound ≤ p)
    (positionBound : position < bound) (floorBound : recentFloor < bound)
    (differenceBound : difference < bound)
    (oldBoolean : Square old old)
    (equation : (position : F) - (recentFloor : F) =
      (difference : F) - old * (bound : F)) :
    old = (if position < recentFloor then 1 else 0) := by
  rcases boolean_sound old oldBoolean with zero | one
  · have order := comparison_lift (F := F) (p := p)
      (a := recentFloor) (b := position) (difference := difference) false
      capacity floorBound positionBound differenceBound (by simpa [zero] using equation)
    have recent : recentFloor ≤ position := order.mp rfl
    simp [zero, Nat.not_lt.mpr recent]
  · have order := comparison_lift (F := F) (p := p)
      (a := recentFloor) (b := position) (difference := difference) true
      capacity floorBound positionBound differenceBound (by simpa [one] using equation)
    have aged : position < recentFloor := by
      have notRecent : ¬ recentFloor ≤ position := by
        intro recent
        have impossible := order.mpr recent
        cases impossible
      omega
    simp [one, aged]

/-- Compose bounded comparison with the spend branch gates. This removes the
abstract `oldCorrect` premise from `branch_sound`; actual row membership and
the range decompositions still have to discharge the explicit local premises. -/
theorem bounded_branch_sound {p bound position recentFloor difference : Nat}
    [CharP F p]
    (dummy history amount nullifier realNullifier syntheticNullifier computedRoot anchor old : F)
    (capacity : 2 * bound ≤ p)
    (positionBound : position < bound) (floorBound : recentFloor < bound)
    (differenceBound : difference < bound)
    (dummyBoolean : Square dummy dummy) (oldBoolean : Square old old)
    (selected : nullifier = dummy * syntheticNullifier + (1 - dummy) * realNullifier)
    (anchorGate : (1 - dummy) * (computedRoot - anchor) = 0)
    (amountGate : dummy * amount = 0)
    (historyGate : history = (1 - dummy) * old)
    (equation : (position : F) - (recentFloor : F) =
      (difference : F) - old * (bound : F)) :
    BranchSpec dummy history amount nullifier realNullifier syntheticNullifier
      computedRoot anchor position recentFloor := by
  exact branch_sound dummy history amount nullifier realNullifier syntheticNullifier
    computedRoot anchor old position recentFloor dummyBoolean selected anchorGate
    amountGate historyGate
    (history_comparison_sound old capacity positionBound floorBound differenceBound
      oldBoolean equation)

/-- Every legal bounded position/floor pair extends to the comparison gates.
The difference is constructed, not assumed to exist. This is local algebraic
completeness; allocating its bits and compiler auxiliaries is a separate join. -/
theorem history_comparison_complete (bound position recentFloor : Nat)
    (positionBound : position < bound) (floorBound : recentFloor < bound) :
    ∃ difference : Nat, difference < bound ∧
      Square (if position < recentFloor then (1 : F) else 0)
        (if position < recentFloor then (1 : F) else 0) ∧
      (position : F) - (recentFloor : F) = (difference : F) -
        (if position < recentFloor then (1 : F) else 0) * (bound : F) := by
  have borrow : (borrowNat recentFloor position : F) =
      (if position < recentFloor then 1 else 0) := by
    by_cases recent : recentFloor ≤ position
    · simp [borrowNat, recent, Nat.not_lt.mpr recent]
    · have aged : position < recentFloor := by omega
      simp [borrowNat, recent, aged]
  refine ⟨differenceNat bound recentFloor position,
    differenceNat_bound bound recentFloor position floorBound positionBound, ?_, ?_⟩
  · split_ifs <;> simp [Square]
  · simpa [borrow] using
      (differenceNat_equation (F := F) bound recentFloor position floorBound positionBound)

/-- The required input is the real branch because its constructor fixes the
selector to zero. This is stronger than assuming an arbitrary selector is a bit. -/
theorem required_input_sound
    (history amount nullifier realNullifier syntheticNullifier computedRoot anchor : F)
    (position recentFloor : Nat)
    (legal : BranchSpec 0 history amount nullifier realNullifier syntheticNullifier
      computedRoot anchor position recentFloor) :
    nullifier = realNullifier ∧ computedRoot = anchor ∧
      history = (if position < recentFloor then 1 else 0) := by
  rcases legal with ⟨_, hn, ha, hh⟩ | ⟨impossible, _⟩
  · exact ⟨hn, ha, hh⟩
  · exact False.elim (zero_ne_one impossible)

#print axioms branch_sound
#print axioms branch_gates_complete
#print axioms history_comparison_sound
#print axioms bounded_branch_sound
#print axioms history_comparison_complete
#print axioms required_input_sound

end ShielddSecurity.Spend
