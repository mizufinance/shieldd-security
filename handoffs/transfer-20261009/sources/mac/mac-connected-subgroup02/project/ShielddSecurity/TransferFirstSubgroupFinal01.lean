import ShielddSecurity.TransferFirstSubgroupAssertionCompletion01

set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferFirstSubgroupFinal01
open Compiler CompilerCompletion CompilerIndexed01 TransferFirstSubgroupData01
open TransferFirstSubgroupCertificates01 TransferFirstSubgroupCompletion01

variable {F : Type} [Field F] [CharP F p]

theorem emitted_append (left right : List Step) : emitted (left++right)=emitted left++emitted right := by
  induction left with
  | nil => rfl
  | cons step tail ih => simp only [List.cons_append,emitted,ih,List.append_assoc]

theorem assertion_rows_complete (rho : Nat → F)
    (truth : ∀ ports ∈ graph.assertions,
      expressionValue rho (expressions ports.1)=expressionValue rho (expressions ports.2)) :
    Satisfies rho (emitted assertionSteps) := by
  have legalSteps := TransferFirstSubgroupAssertionCompletion01.assertion_steps_legal rho truth
  have isEquality : ∀ step ∈ assertionSteps, ∃ left right, step=.equal left right := by
    intro step member
    simp only [assertionSteps,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h <;> subst step
    all_goals exact ⟨_,_,rfl⟩
  have complete : ∀ steps : List Step, (∀ step ∈ steps, ∃ left right, step=.equal left right) →
      (∀ step ∈ steps,step.Legal rho) → Satisfies rho (emitted steps) := by
    intro steps
    induction steps with
    | nil => intro shape legal row member; cases member
    | cons step tail ih =>
        intro shape legal row member
        obtain ⟨left,right,equal⟩ := shape step (by simp)
        subst step
        have rowResult : Satisfies rho (Step.rows (.equal left right)) :=
          step_complete (.equal left right) rho trivial (legal _ (by simp))
        simp only [emitted,List.mem_append] at member
        rcases member with here | later
        · exact rowResult row here
        · exact ih (by intro s h; exact shape s (List.mem_cons_of_mem _ h))
            (by intro s h; exact legal s (List.mem_cons_of_mem _ h)) row later
  exact complete assertionSteps isEquality legalSteps

theorem all_emitted_complete (inputs : Nat → F) (four : (4:F)≠0)
    (sourceAssertions : ∀ ports ∈ graph.assertions,
      SourceGraphEvaluation.values graph inputs ports.1=SourceGraphEvaluation.values graph inputs ports.2) :
    Satisfies (completed inputs) (emitted allSteps) := by
  have arithmetic : Satisfies (completed inputs) (emitted arithmeticSteps) := by
    have result := run_complete (boundary inputs) arithmeticSteps [0,copy] [] ordered (legal _)
      (by intro row member; cases member)
    simpa [completed] using result
  have valuesEqual := completed_values inputs four
  have assertions : Satisfies (completed inputs) (emitted assertionSteps) :=
    assertion_rows_complete _ (by intro ports member; rw [congrFun valuesEqual ports.1,congrFun valuesEqual ports.2]; exact sourceAssertions ports member)
  intro row member
  simp only [allSteps,emitted_append,List.mem_append] at member
  rcases member with (materialized | assertion) | copyRow
  · apply arithmetic row
    simp only [arithmeticSteps,emitted_append,List.mem_append]
    exact Or.inl materialized
  · exact assertions row assertion
  · apply arithmetic row
    simp only [arithmeticSteps,emitted_append,List.mem_append]
    exact Or.inr copyRow

/-- The assertion premise is an independent arithmetic-graph property. The
Windows subgroup semantic bridge must discharge it for legal native inputs. -/
theorem constructive_slice_complete (inputs : Nat → F) (four : (4:F)≠0)
    (sourceAssertions : ∀ ports ∈ graph.assertions,
      SourceGraphEvaluation.values graph inputs ports.1=SourceGraphEvaluation.values graph inputs ports.2) :
    Satisfies (completed inputs) originalRows.toList ∧
      (∀ input < 22735, completed inputs (3+input)=inputs input) ∧
      completed inputs 0=1 ∧ completed inputs copy=1 := by
  have allRows := all_emitted_complete inputs four sourceAssertions
  have linked : completed inputs copy=completed inputs 0 := (completed_copy inputs).trans (completed_one inputs).symm
  refine ⟨?_,original_input_preserved inputs,completed_one inputs,completed_copy inputs⟩
  intro actual member
  obtain ⟨expected,present,left,right⟩ := original_reverse_coverage actual member
  have result := allRows expected present
  rw [← canonical_equal (completed inputs) _ _ left,← canonical_equal (completed inputs) _ _ right] at result
  simpa only [eval_unoutline (completed inputs) copy _ linked] using result

end ShielddSecurity.TransferFirstSubgroupFinal01

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupFinal01.emitted_append
#print axioms ShielddSecurity.TransferFirstSubgroupFinal01.emitted_append

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupFinal01.assertion_rows_complete
#print axioms ShielddSecurity.TransferFirstSubgroupFinal01.assertion_rows_complete

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupFinal01.all_emitted_complete
#print axioms ShielddSecurity.TransferFirstSubgroupFinal01.all_emitted_complete

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupFinal01.constructive_slice_complete
#print axioms ShielddSecurity.TransferFirstSubgroupFinal01.constructive_slice_complete
