import ShielddSecurity.CompilerSubgroupClosure83
import ShielddSecurity.CapturedFirstSubgroup81
import ShielddSecurity.TransferFirstSubgroupCompletion01
import ShielddSecurity.PoseidonCallComposition04
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerSubgroupConstructor84
open Compiler CompilerCompletion CompilerIndexed01
variable {F : Type} [Field F]
theorem independent_source_complete (graph : SourceGraph 22735 80) (d negative : Int)
    (initial : Group.Point F) (remaining : Nat → F) (imaginary : F)
    (negativeOne : (negative:F)=-1) (shape : CompilerSubgroupSource80.Matches graph d negative)
    (nonSquare : Group.NoUnitSquare (d:F)) (imaginarySquare : imaginary*imaginary=-1)
    (valid : Group.OnCurve (d:F) initial) :
    ∀ assertion ∈ graph.assertions,
      SourceGraphEvaluation.values graph (CompilerSubgroupSource80.constructedInputs (d:F) initial remaining) assertion.1 =
      SourceGraphEvaluation.values graph (CompilerSubgroupSource80.constructedInputs (d:F) initial remaining) assertion.2 :=
  CompilerSubgroupSource80.graph_assertions_complete graph d negative initial remaining negativeOne shape valid
    (by intro index _; exact CompilerSubgroupClosure83.trace_denominators (d:F) imaginary nonSquare imaginarySquare initial valid index)
-- Reverse transport is proved from exact emitted row coverage, not reversed soundness.
theorem assertion_emitted (rho : Nat → F)
    (truth : ∀ ports ∈ TransferFirstSubgroupData01.graph.assertions,
      expressionValue rho (TransferFirstSubgroupData01.expressions ports.1)=
      expressionValue rho (TransferFirstSubgroupData01.expressions ports.2)) :
    Satisfies rho (emitted TransferFirstSubgroupData01.assertionSteps) := by
  intro row member
  simp only [TransferFirstSubgroupData01.assertionSteps,emitted,List.mem_cons,List.not_mem_nil,
    List.append_nil,List.mem_append,Step.rows,or_false] at member
  rcases member with h | h | h | h | h | h
  · subst row
    have equal := truth (⟨25,by decide⟩,⟨28,by decide⟩) (by decide +kernel)
    change Square (eval rho (subtract _ _)) (eval rho [])
    rw [eval_subtract,show eval rho _=eval rho _ from equal]
    simp [Square,eval]
  · subst row
    have equal := truth (⟨13,by decide⟩,⟨37,by decide⟩) (by decide +kernel)
    change Square (eval rho (subtract _ _)) (eval rho [])
    rw [eval_subtract,show eval rho _=eval rho _ from equal]
    simp [Square,eval]
  · subst row
    have equal := truth (⟨17,by decide⟩,⟨54,by decide⟩) (by decide +kernel)
    change Square (eval rho (subtract _ _)) (eval rho [])
    rw [eval_subtract,show eval rho _=eval rho _ from equal]
    simp [Square,eval]
  · subst row
    have equal := truth (⟨21,by decide⟩,⟨71,by decide⟩) (by decide +kernel)
    change Square (eval rho (subtract _ _)) (eval rho [])
    rw [eval_subtract,show eval rho _=eval rho _ from equal]
    simp [Square,eval]
  · subst row
    have equal := truth (⟨0,by decide⟩,⟨76,by decide⟩) (by decide +kernel)
    change Square (eval rho (subtract _ _)) (eval rho [])
    rw [eval_subtract,show eval rho _=eval rho _ from equal]
    simp [Square,eval]
  · subst row
    have equal := truth (⟨1,by decide⟩,⟨79,by decide⟩) (by decide +kernel)
    change Square (eval rho (subtract _ _)) (eval rho [])
    rw [eval_subtract,show eval rho _=eval rho _ from equal]
    simp [Square,eval]
variable [CharP F TransferFirstSubgroupData01.p]
theorem original_from_arithmetic (rho : Nat → F) (linked : rho TransferFirstSubgroupData01.copy=rho 0)
    (arithmetic : Satisfies rho (emitted TransferFirstSubgroupData01.arithmeticSteps))
    (truth : ∀ ports ∈ TransferFirstSubgroupData01.graph.assertions,
      expressionValue rho (TransferFirstSubgroupData01.expressions ports.1)=
      expressionValue rho (TransferFirstSubgroupData01.expressions ports.2)) :
    Satisfies rho TransferFirstSubgroupData01.originalRows.toList := by
  have materialized : Satisfies rho (emitted TransferFirstSubgroupData01.materializedSteps) := by
    intro row member
    apply arithmetic row
    simpa only [TransferFirstSubgroupData01.arithmeticSteps,PoseidonCallComposition04.emitted_append,
      List.mem_append] using Or.inl member
  have copied : Satisfies rho (emitted [TransferFirstSubgroupData01.copyStep]) := by
    intro row member
    simp only [emitted,Step.rows,TransferFirstSubgroupData01.copyStep,List.append_nil,List.mem_singleton] at member
    subst row
    simp [subtract,scaleLinear,eval,Square]
  have all : Satisfies rho (emitted TransferFirstSubgroupData01.allSteps) := by
    intro row member
    simp only [TransferFirstSubgroupData01.allSteps,PoseidonCallComposition04.emitted_append,List.mem_append] at member
    rcases member with (first | second) | last
    · exact materialized row first
    · exact assertion_emitted rho truth row second
    · exact copied row last
  intro actual member
  obtain ⟨expected,present,left,right⟩:=TransferFirstSubgroupCertificates01.original_reverse_coverage actual member
  have result:=all expected present
  rw [←canonical_equal rho _ _ left,←canonical_equal rho _ _ right] at result
  simpa only [eval_unoutline rho TransferFirstSubgroupData01.copy _ linked] using result
-- The arbitrary arithmetic base is used directly: no public/committed boundary overwrite.
def completed (base : Nat → F) : Nat → F := run base TransferFirstSubgroupData01.arithmeticSteps
theorem completed_arithmetic (base : Nat → F) (linked : base TransferFirstSubgroupData01.copy=base 0) :
    Satisfies (completed base) TransferFirstSubgroupData01.arithmeticRows.toList :=
  (original_rows_complete base TransferFirstSubgroupData01.arithmeticSteps [0,TransferFirstSubgroupData01.copy]
    TransferFirstSubgroupData01.arithmeticRows.toList TransferFirstSubgroupData01.copy
    TransferFirstSubgroupCompletion01.ordered (TransferFirstSubgroupCompletion01.legal base)
    (by simp) (by simp) linked TransferFirstSubgroupCertificates01.arithmetic_reverse_coverage).1
theorem completed_emitted (base : Nat → F) :
    Satisfies (completed base) (emitted TransferFirstSubgroupData01.arithmeticSteps) := by
  simpa only [List.nil_append] using run_complete base TransferFirstSubgroupData01.arithmeticSteps
    [0,TransferFirstSubgroupData01.copy] [] TransferFirstSubgroupCompletion01.ordered
    (TransferFirstSubgroupCompletion01.legal base) (by intro row member; cases member)
omit [CharP F TransferFirstSubgroupData01.p] in
theorem completed_copy (base : Nat → F) (linked : base TransferFirstSubgroupData01.copy=base 0) :
    completed base TransferFirstSubgroupData01.copy=completed base 0 := by
  have kept:=run_preserves base TransferFirstSubgroupData01.arithmeticSteps [0,TransferFirstSubgroupData01.copy]
    [] TransferFirstSubgroupCompletion01.ordered
  rw [show completed base TransferFirstSubgroupData01.copy=base TransferFirstSubgroupData01.copy from kept _ (by simp),
    show completed base 0=base 0 from kept _ (by simp),linked]
theorem completed_values (base : Nat → F) (one : base 0=1)
    (linked : base TransferFirstSubgroupData01.copy=base 0) :
    (fun index => expressionValue (completed base) (TransferFirstSubgroupData01.expressions index))=
      SourceGraphEvaluation.values TransferFirstSubgroupData01.graph
        (fun input => eval (completed base) (TransferFirstSubgroupData01.inputTerms input)) := by
  have sat:=unoutline_rows_sound (completed base) TransferFirstSubgroupData01.copy
    TransferFirstSubgroupData01.arithmeticRows.toList (completed_arithmetic base linked)
    (checkRowAt_sound _ _ _ _ TransferFirstSubgroupCertificates01.arithmetic_copy_checked)
  have kept:=run_preserves base TransferFirstSubgroupData01.arithmeticSteps [0,TransferFirstSubgroupData01.copy]
    [] TransferFirstSubgroupCompletion01.ordered
  exact CompilerGraphEvaluationSoundness.compiled_values_eq_evaluation TransferFirstSubgroupData01.graph _
    TransferFirstSubgroupData01.inputTerms TransferFirstSubgroupData01.expressions
    TransferFirstSubgroupCertificates01.node_certificates (completed base)
    ((kept 0 (by simp)).trans one) (CompilerArithmeticTransport41.four_ne_zero (F:=F)) sat
end ShielddSecurity.CompilerSubgroupConstructor84
