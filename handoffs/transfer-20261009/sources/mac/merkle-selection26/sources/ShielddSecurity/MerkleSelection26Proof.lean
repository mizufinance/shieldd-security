import ShielddSecurity.MerkleSelection26Data
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleSelection26Proof
open Compiler CompilerCompletion CompilerIndexed01 CompilerSegmentCompletion11
open CapturedInitial73419Generic01 (p copy writeCheck supportCheck makeSegment)
open MerkleSelection26Data
theorem order_checked : CompilerOrder.checkOrder [0,copy] [] steps=true := by decide +kernel
theorem coverage_checked : checkOriginalCoverage p copy originalRows.toArray (emitted steps).toArray (List.range 13).toArray=true := by decide +kernel
theorem writes_checked : writeCheck 25460 25472 steps=true := by decide +kernel
theorem support_checked : supportCheck 25472 originalRows=true := by decide +kernel
theorem counts : materializedSteps.length=6 ∧ steps.length=7 ∧ arithmeticRows.length=12 ∧ originalRows.length=13 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
omit [CharP F p] in
theorem legal (base : Nat → F) : Legal base steps := by
  simp [steps,materializedSteps,step0,step1,step2,step3,step4,step5,TransferPoseidonCall04Shared01.copyStep,Legal,Step.Legal]
theorem completed (base : Nat → F) (linked : base copy=base 0) : Satisfies (run base steps) originalRows :=
  (original_rows_complete base steps [0,copy] originalRows copy
    (CompilerOrder.checked_order _ _ _ order_checked) (legal base) (by simp) (by simp) linked
    (checkOriginalCoverage_sound p copy _ _ _ coverage_checked)).1
def segment : Segment F copy := makeSegment steps originalRows 25460 25472 writes_checked support_checked completed
theorem outside (base : Nat → F) (column : Nat) (bound : column<25460 ∨ 25472≤column) :
    run base steps column=base column := CompilerSegmentCompletion11.outside copy segment base column bound
theorem originals (base : Nat → F) (i : Nat) (bound : i<22735) : run base steps (3+i)=base (3+i) := outside base _ (Or.inl (by omega))
end ShielddSecurity.MerkleSelection26Proof

set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.order_checked
#print axioms ShielddSecurity.MerkleSelection26Proof.order_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.coverage_checked
#print axioms ShielddSecurity.MerkleSelection26Proof.coverage_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.writes_checked
#print axioms ShielddSecurity.MerkleSelection26Proof.writes_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.support_checked
#print axioms ShielddSecurity.MerkleSelection26Proof.support_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.counts
#print axioms ShielddSecurity.MerkleSelection26Proof.counts
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.legal
#print axioms ShielddSecurity.MerkleSelection26Proof.legal
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.completed
#print axioms ShielddSecurity.MerkleSelection26Proof.completed
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.segment
#print axioms ShielddSecurity.MerkleSelection26Proof.segment
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.outside
#print axioms ShielddSecurity.MerkleSelection26Proof.outside
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Proof.originals
#print axioms ShielddSecurity.MerkleSelection26Proof.originals
