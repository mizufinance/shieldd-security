import ShielddSecurity.Tree

set_option maxHeartbeats 200000

namespace ShielddSecurity.TreeBinding

variable {F : Type} [Field F]

structure Step (F : Type) where
  low : Bool
  high : Bool
  first : F
  second : F
  third : F

def root (hash : Nat → List F → F) (level : Nat) (node : F) : List (Step F) → F
  | [] => node
  | step :: rest => root hash (level + 1)
      (hash level (Tree.children step.low step.high node step.first step.second step.third)) rest

/-- Two paths follow the same leaf position, but siblings may differ. -/
inductive Aligned : List (Step F) → List (Step F) → Prop
  | nil : Aligned [] []
  | cons (left right : Step F) (ls rs : List (Step F))
      (low : left.low = right.low) (high : left.high = right.high)
      (rest : Aligned ls rs) : Aligned (left :: ls) (right :: rs)

theorem children_preserve_node (low high : Bool) (left right a b c d e f : F)
    (same : Tree.children low high left a b c = Tree.children low high right d e f) :
    left = right := by
  cases high with
  | false =>
      cases low with
      | false =>
          have selected := congrArg (fun values : List F => values[0]?) same
          simpa [Tree.children] using selected
      | true =>
          have selected := congrArg (fun values : List F => values[1]?) same
          simpa [Tree.children] using selected
  | true =>
      cases low with
      | false =>
          have selected := congrArg (fun values : List F => values[2]?) same
          simpa [Tree.children] using selected
      | true =>
          have selected := congrArg (fun values : List F => values[3]?) same
          simpa [Tree.children] using selected

theorem children_length (low high : Bool) (node a b c : F) :
    (Tree.children low high node a b c).length = 4 := by
  cases low <;> cases high <;> simp [Tree.children]

/-- Equal roots at the same leaf position with distinct leaves produce an
explicit collision at one ordered four-child hash input. This is collision
witness extraction, not a universal injectivity assumption about Poseidon.
Runtime domains/height/position and actual hash/circuit joins remain separate. -/
theorem equal_root_collision (hash : Nat → List F → F) (level : Nat)
    (leftPath rightPath : List (Step F)) (aligned : Aligned leftPath rightPath)
    (leftLeaf rightLeaf : F) (different : leftLeaf ≠ rightLeaf)
    (equalRoot : root hash level leftLeaf leftPath = root hash level rightLeaf rightPath) :
    ∃ collisionLevel leftInput rightInput,
      level ≤ collisionLevel ∧ collisionLevel < level + leftPath.length ∧
      leftInput.length = 4 ∧ rightInput.length = 4 ∧
      leftInput ≠ rightInput ∧ hash collisionLevel leftInput = hash collisionLevel rightInput := by
  classical
  induction aligned generalizing level leftLeaf rightLeaf with
  | nil => exact False.elim (different equalRoot)
  | cons left right ls rs low high rest ih =>
      let leftInput := Tree.children left.low left.high leftLeaf left.first left.second left.third
      let rightInput := Tree.children right.low right.high rightLeaf right.first right.second right.third
      have inputsDifferent : leftInput ≠ rightInput := by
        intro same
        have nodes : leftLeaf = rightLeaf := children_preserve_node left.low left.high
          leftLeaf rightLeaf left.first left.second left.third right.first right.second right.third
          (by simpa [leftInput, rightInput, ← low, ← high] using same)
        exact different nodes
      by_cases collision : hash level leftInput = hash level rightInput
      · exact ⟨level, leftInput, rightInput, Nat.le_refl level, by simp,
          children_length _ _ _ _ _ _, children_length _ _ _ _ _ _, inputsDifferent, collision⟩
      · obtain ⟨collisionLevel, firstInput, secondInput, lower, upper, firstLength,
            secondLength, distinct, sameHash⟩ :=
          ih (level + 1) (hash level leftInput) (hash level rightInput) collision equalRoot
        refine ⟨collisionLevel, firstInput, secondInput, by omega, ?_,
          firstLength, secondLength, distinct, sameHash⟩
        simp only [List.length_cons]
        omega

/-- The deployed tree framing uses one level field followed by four children.
The hash interpretation is fixed throughout both paths; this extracts a collision
at its actual five-field input without asserting hash injectivity. -/
theorem framed_root_collision (actualHash : List F → F) (level : Nat)
    (leftPath rightPath : List (Step F)) (aligned : Aligned leftPath rightPath)
    (leftLeaf rightLeaf : F) (different : leftLeaf ≠ rightLeaf)
    (equalRoot : root (fun i children => actualHash (((i + 1 : Nat) : F) :: children))
      level leftLeaf leftPath =
      root (fun i children => actualHash (((i + 1 : Nat) : F) :: children))
      level rightLeaf rightPath) :
    ∃ collisionLevel leftInput rightInput,
      level ≤ collisionLevel ∧ collisionLevel < level + leftPath.length ∧
      leftInput.length = 5 ∧ rightInput.length = 5 ∧
      leftInput ≠ rightInput ∧ actualHash leftInput = actualHash rightInput := by
  obtain ⟨i, left, right, lower, upper, leftLength, rightLength, distinct, same⟩ :=
    equal_root_collision _ level leftPath rightPath aligned leftLeaf rightLeaf different equalRoot
  refine ⟨i, ((i + 1 : Nat) : F) :: left, ((i + 1 : Nat) : F) :: right,
    lower, upper, by simp [leftLength], by simp [rightLength], ?_, same⟩
  intro equalInputs
  exact distinct (List.cons.inj equalInputs).2

set_option pp.all true in
#check @children_preserve_node
#print axioms children_preserve_node
set_option pp.all true in
#check @children_length
#print axioms children_length
set_option pp.all true in
#check @equal_root_collision
#print axioms equal_root_collision

set_option pp.all true in
#check @framed_root_collision
#print axioms framed_root_collision

end ShielddSecurity.TreeBinding
