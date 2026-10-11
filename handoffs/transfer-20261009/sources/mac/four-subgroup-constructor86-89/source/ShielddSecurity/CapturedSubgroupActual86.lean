import ShielddSecurity.CompilerSubgroupConstructor84
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupActual86
open Compiler CompilerCompletion CompilerIndexed01
noncomputable def reversedCheck : Bool := checkOriginalCoverage TransferFirstSubgroupData01.p 0
  TransferFirstSubgroupData01.emittedArithmetic
  (unoutlineRows TransferFirstSubgroupData01.copy TransferFirstSubgroupData01.arithmeticRows.toList).toArray
  TransferFirstSubgroupData01.arithmeticMapping
theorem reversed_checked : reversedCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F TransferFirstSubgroupData01.p]
theorem emitted_from_actual (rho : Nat → F)
    (actual : Satisfies rho TransferFirstSubgroupData01.arithmeticRows.toList) :
    Satisfies rho (emitted TransferFirstSubgroupData01.arithmeticSteps) := by
  have normalized:=unoutline_rows_sound rho TransferFirstSubgroupData01.copy
    TransferFirstSubgroupData01.arithmeticRows.toList actual
    (checkRowAt_sound _ _ _ _ TransferFirstSubgroupCertificates01.arithmetic_copy_checked)
  have coverage:=checkOriginalCoverage_sound TransferFirstSubgroupData01.p 0
    TransferFirstSubgroupData01.emittedArithmetic
    (unoutlineRows TransferFirstSubgroupData01.copy TransferFirstSubgroupData01.arithmeticRows.toList).toArray
    TransferFirstSubgroupData01.arithmeticMapping reversed_checked
  intro row member
  have memberArray : row∈TransferFirstSubgroupData01.emittedArithmetic.toList := by
    simpa only [TransferFirstSubgroupCertificates01.arithmetic_emitted_identity] using member
  obtain ⟨expected,present,left,right⟩:=coverage row memberArray
  have result:=normalized expected (by simpa only [List.toList_toArray] using present)
  rw [←canonical_equal rho _ _ left,←canonical_equal rho _ _ right] at result
  simpa only [eval_unoutline rho 0 _ rfl] using result
theorem values_from_actual (rho : Nat → F) (one : rho 0=1)
    (actual : Satisfies rho TransferFirstSubgroupData01.arithmeticRows.toList) :
    (fun index => expressionValue rho (TransferFirstSubgroupData01.expressions index))=
      SourceGraphEvaluation.values TransferFirstSubgroupData01.graph
        (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input)) :=
  CompilerGraphEvaluationSoundness.compiled_values_eq_evaluation TransferFirstSubgroupData01.graph _
    TransferFirstSubgroupData01.inputTerms TransferFirstSubgroupData01.expressions
    TransferFirstSubgroupCertificates01.node_certificates rho one
    (CompilerArithmeticTransport41.four_ne_zero (F:=F))
    (unoutline_rows_sound rho TransferFirstSubgroupData01.copy TransferFirstSubgroupData01.arithmeticRows.toList
      actual (checkRowAt_sound _ _ _ _ TransferFirstSubgroupCertificates01.arithmetic_copy_checked))
-- This fixed-point equation binds only independently constructed source input roles; no row truth is assumed.
theorem original_from_constructed_inputs (rho : Nat → F) (initial : Group.Point F) (imaginary : F)
    (one : rho 0=1) (linked : rho TransferFirstSubgroupData01.copy=rho 0)
    (actual : Satisfies rho TransferFirstSubgroupData01.arithmeticRows.toList)
    (roles : (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input))=
      CompilerSubgroupSource80.constructedInputs (CapturedFirstSubgroup81.d:F) initial
        (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input)))
    (valid : Group.OnCurve (CapturedFirstSubgroup81.d:F) initial)
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    Satisfies rho TransferFirstSubgroupData01.originalRows.toList := by
  have values:=values_from_actual rho one actual
  have truth:=CompilerSubgroupConstructor84.independent_source_complete TransferFirstSubgroupData01.graph
    CapturedFirstSubgroup81.d CapturedFirstSubgroup81.negative initial
    (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input)) imaginary
    (CompilerSubgroupSource80.modulus_negative_one (F:=F)) CapturedFirstSubgroup81.shape nonSquare imaginarySquare valid
  apply CompilerSubgroupConstructor84.original_from_arithmetic rho linked (emitted_from_actual rho actual)
  intro ports member
  have equal:=truth ports member
  rw [←roles] at equal
  exact (congrFun values ports.1).trans (equal.trans (congrFun values ports.2).symm)
end ShielddSecurity.CapturedSubgroupActual86

set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupActual86.reversedCheck
#print axioms ShielddSecurity.CapturedSubgroupActual86.reversedCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupActual86.reversed_checked
#print axioms ShielddSecurity.CapturedSubgroupActual86.reversed_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupActual86.emitted_from_actual
#print axioms ShielddSecurity.CapturedSubgroupActual86.emitted_from_actual
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupActual86.values_from_actual
#print axioms ShielddSecurity.CapturedSubgroupActual86.values_from_actual
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupActual86.original_from_constructed_inputs
#print axioms ShielddSecurity.CapturedSubgroupActual86.original_from_constructed_inputs
