import ShielddSecurity.CompilerCompletion

set_option maxHeartbeats 220000
set_option maxRecDepth 2048

namespace ShielddSecurity.CompilerPatchCommutation

variable {F : Type} [Field F]

theorem values_congr (base first second : Nat → F) (fresh : List Nat)
    (agree : ∀ column ∈ fresh, first column = second column) :
    patchAssignment base first fresh = patchAssignment base second fresh := by
  funext column
  by_cases member : column ∈ fresh
  · simp only [patchAssignment,if_pos member,agree column member]
  · simp only [patchAssignment,if_neg member]

theorem patches_commute (base first second : Nat → F) (firstWrites secondWrites : List Nat)
    (disjoint : ∀ column ∈ firstWrites, column ∉ secondWrites) :
    patchAssignment (patchAssignment base first firstWrites) second secondWrites =
      patchAssignment (patchAssignment base second secondWrites) first firstWrites := by
  funext column
  by_cases a : column ∈ firstWrites
  · have b := disjoint column a
    simp only [patchAssignment,if_pos a,if_neg b]
  · by_cases b : column ∈ secondWrites
    · simp only [patchAssignment,if_neg a,if_pos b]
    · simp only [patchAssignment,if_neg a,if_neg b]

theorem eval_patch (base values : Nat → F) (fresh : List Nat) (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 ∉ fresh) :
    eval (patchAssignment base values fresh) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact patchAssignment_preserves base values fresh term.1 (outside term member)

def reads : CompilerCompletion.Step → Linear
  | .square input remainder _ => input ++ remainder
  | .product left right remainder _ _ => left ++ right ++ remainder
  | .equal left right => left ++ right
  | .squareEqual input target => input ++ target

def Separated (fresh : List Nat) (step : CompilerCompletion.Step) : Prop :=
  (∀ term ∈ reads step, term.1 ∉ fresh) ∧ (∀ column ∈ step.writes, column ∉ fresh)

theorem step_commutes (base values : Nat → F) (fresh : List Nat)
    (step : CompilerCompletion.Step) (separated : Separated fresh step) :
    step.run (patchAssignment base values fresh) = patchAssignment (step.run base) values fresh := by
  have disjoint : ∀ column ∈ fresh, column ∉ step.writes := by
    intro column member written
    exact separated.2 column written member
  cases step with
  | square input remainder output =>
      have inputValue := eval_patch base values fresh input
        (by intro term member; exact separated.1 term (List.mem_append_left remainder member))
      have remainderValue := eval_patch base values fresh remainder
        (by intro term member; exact separated.1 term (List.mem_append_right input member))
      simp only [CompilerCompletion.Step.run,CompilerCompletion.extendSquare,inputValue,remainderValue]
      exact patches_commute base values (fun _ => eval base input ^ 2 - eval base remainder)
        fresh [output] disjoint
  | product left right remainder output auxiliary =>
      have leftValue := eval_patch base values fresh left (by
        intro term member
        exact separated.1 term (List.mem_append_left remainder (List.mem_append_left right member)))
      have rightValue := eval_patch base values fresh right (by
        intro term member
        exact separated.1 term (List.mem_append_left remainder (List.mem_append_right left member)))
      have remainderValue := eval_patch base values fresh remainder (by
        intro term member
        exact separated.1 term (List.mem_append_right (left ++ right) member))
      have same : patchAssignment (patchAssignment base values fresh)
          (ScalarCompletion.productValues (patchAssignment base values fresh) left right remainder output auxiliary)
          [output,auxiliary] =
        patchAssignment (patchAssignment base values fresh)
          (ScalarCompletion.productValues base left right remainder output auxiliary) [output,auxiliary] := by
        apply values_congr
        intro column member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with atOutput | atAuxiliary
        · simp only [ScalarCompletion.productValues,if_pos atOutput,leftValue,rightValue,remainderValue]
        · by_cases atOutput : column = output
          · simp only [ScalarCompletion.productValues,if_pos atOutput,leftValue,rightValue,remainderValue]
          · simp only [ScalarCompletion.productValues,if_neg atOutput,if_pos atAuxiliary,leftValue,rightValue]
      change patchAssignment (patchAssignment base values fresh)
          (ScalarCompletion.productValues (patchAssignment base values fresh) left right remainder output auxiliary)
          [output,auxiliary] =
        patchAssignment (patchAssignment base (ScalarCompletion.productValues base left right remainder output auxiliary)
          [output,auxiliary]) values fresh
      rw [same]
      exact patches_commute base values (ScalarCompletion.productValues base left right remainder output auxiliary)
        fresh [output,auxiliary] disjoint
  | equal left right => rfl
  | squareEqual input target => rfl

theorem run_commutes (base values : Nat → F) (fresh : List Nat)
    (steps : List CompilerCompletion.Step) (separated : ∀ step ∈ steps, Separated fresh step) :
    CompilerCompletion.run (patchAssignment base values fresh) steps =
      patchAssignment (CompilerCompletion.run base steps) values fresh := by
  induction steps generalizing base with
  | nil => rfl
  | cons step tail ih =>
      simp only [CompilerCompletion.run]
      rw [step_commutes base values fresh step (separated step (List.mem_cons_self))]
      exact ih (step.run base) (by intro item member; exact separated item (List.mem_cons_of_mem step member))

theorem root_bits_patch (base : Nat → F) (root start : Nat) (value : F) (bits : List Bool)
    (outsideRoot : root < start ∨ start + bits.length ≤ root) :
    writeBits (patchAssignment base (fun _ => value) [root]) start bits =
      patchAssignment base (fun column => if column = root then value
        else if bits[column-start]?.getD false then 1 else 0) ([root] ++ List.range' start bits.length) := by
  funext column
  by_cases atRoot : column = root
  · subst column
    have outside : ¬ (start ≤ root ∧ root < start + bits.length) := by omega
    simp only [writeBits,if_neg outside,patchAssignment,List.mem_append,List.mem_singleton,
      or_true,true_or,if_true,if_pos rfl]
  · by_cases inside : start ≤ column ∧ column < start + bits.length
    · have member : column ∈ List.range' start bits.length := List.mem_range'_1.mpr inside
      simp only [writeBits,if_pos inside,patchAssignment,List.mem_append,List.mem_singleton,
        atRoot,member,false_or,if_true,if_false]
    · have absent : column ∉ List.range' start bits.length := by
        intro member
        exact inside (List.mem_range'_1.mp member)
      simp only [writeBits,if_neg inside,patchAssignment,List.mem_append,List.mem_singleton,
        atRoot,absent,false_or,if_false,if_neg atRoot]

set_option pp.all true in
#check @values_congr
#print axioms values_congr
set_option pp.all true in
#check @patches_commute
#print axioms patches_commute
set_option pp.all true in
#check @eval_patch
#print axioms eval_patch
set_option pp.all true in
#check @step_commutes
#print axioms step_commutes
set_option pp.all true in
#check @run_commutes
#print axioms run_commutes
set_option pp.all true in
#check @root_bits_patch
#print axioms root_bits_patch

end ShielddSecurity.CompilerPatchCommutation
