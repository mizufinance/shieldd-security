import ShielddSecurity.CompilerSubgroupConstructor84
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFirstSubgroupSeed85
open Compiler CompilerCompletion
variable {F : Type} [Field F]
def seeded (base : Nat → F) (initial : Group.Point F) (column : Nat) : F :=
  if column=14 then (CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) initial).x
  else if column=15 then (CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) initial).y
  else if column=16 then initial.x
  else if column=17 then initial.y
  else if 18≤column ∧ column<21 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) initial (column-18)
  else base column
theorem seeded_outside (base : Nat → F) (initial : Group.Point F) (column : Nat)
    (outside : column<14 ∨ 21≤column) : seeded base initial column=base column := by
  simp [seeded,show column≠14 by omega,show column≠15 by omega,show column≠16 by omega,
    show column≠17 by omega,show ¬(18≤column ∧ column<21) by omega]
theorem writes_upper_checked : (PoseidonCompletion.writes TransferFirstSubgroupData01.arithmeticSteps).all
    (fun column => decide (column<22802))=true := by decide +kernel
variable [CharP F TransferFirstSubgroupData01.p]
def completed (base : Nat → F) (initial : Group.Point F) : Nat → F :=
  CompilerSubgroupConstructor84.completed (seeded base initial)
theorem arithmetic_outside (base : Nat → F) (column : Nat)
    (outside : column<22738 ∨ 22802≤column) : CompilerSubgroupConstructor84.completed base column=base column := by
  apply PoseidonCompletion.run_outside
  intro member
  have lower:=TransferFirstSubgroupCompletion01.writes_lower_bound column member
  have upper:=of_decide_eq_true (List.all_eq_true.mp writes_upper_checked column member)
  omega
theorem original_role (base : Nat → F) (initial : Group.Point F) (input : Nat) (before : input<22735) :
    eval (completed base initial) (TransferFirstSubgroupData01.inputTerms input)=seeded base initial (3+input) := by
  simpa only [TransferFirstSubgroupData01.inputTerms,eval,List.foldl_cons,List.foldl_nil,
    Int.cast_one,one_mul,zero_add,add_zero] using arithmetic_outside (seeded base initial) (3+input) (Or.inl (by omega))
theorem input_identity (base : Nat → F) (initial : Group.Point F) :
    (fun input => eval (completed base initial) (TransferFirstSubgroupData01.inputTerms input))=
    CompilerSubgroupSource80.constructedInputs (CapturedFirstSubgroup81.d:F) initial
      (fun input => eval (completed base initial) (TransferFirstSubgroupData01.inputTerms input)) := by
  funext input
  by_cases e11:input=11
  · subst input; rw [original_role base initial 11 (by decide)]; simp [seeded,CompilerSubgroupSource80.constructedInputs]
  by_cases e12:input=12
  · subst input; rw [original_role base initial 12 (by decide)]; simp [seeded,CompilerSubgroupSource80.constructedInputs]
  by_cases e13:input=13
  · subst input; rw [original_role base initial 13 (by decide)]; simp [seeded,CompilerSubgroupSource80.constructedInputs]
  by_cases e14:input=14
  · subst input; rw [original_role base initial 14 (by decide)]; simp [seeded,CompilerSubgroupSource80.constructedInputs]
  by_cases h:15≤input ∧ input<18
  · rw [original_role base initial input (by omega)]
    simp [CompilerSubgroupSource80.constructedInputs,e11,e12,e13,e14,h,seeded,
      show 3+input≠14 by omega,show 3+input≠15 by omega,show 3+input≠16 by omega,
      show 3+input≠17 by omega,show 18≤3+input ∧ 3+input<21 by omega,
      show 3+input-18=input-15 by omega]
  · simp only [CompilerSubgroupSource80.constructedInputs,if_neg e11,if_neg e12,if_neg e13,if_neg e14,if_neg h]
theorem completed_one (base : Nat → F) (initial : Group.Point F) (one : base 0=1) : completed base initial 0=1 := by
  rw [show completed base initial 0=seeded base initial 0 from arithmetic_outside _ _ (by omega),
    seeded_outside base initial 0 (by omega),one]
theorem seeded_linked (base : Nat → F) (initial : Group.Point F)
    (linked : base TransferFirstSubgroupData01.copy=base 0) :
    seeded base initial TransferFirstSubgroupData01.copy=seeded base initial 0 := by
  rw [seeded_outside base initial TransferFirstSubgroupData01.copy (by decide),seeded_outside base initial 0 (by omega),linked]
theorem completed_original (base : Nat → F) (initial : Group.Point F) (imaginary : F)
    (one : base 0=1) (linked : base TransferFirstSubgroupData01.copy=base 0)
    (valid : Group.OnCurve (CapturedFirstSubgroup81.d:F) initial)
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
    (imaginarySquare : imaginary*imaginary=-1) :
    Satisfies (completed base initial) TransferFirstSubgroupData01.originalRows.toList := by
  have copyLink:=seeded_linked base initial linked
  have values:=CompilerSubgroupConstructor84.completed_values (seeded base initial)
    ((seeded_outside base initial 0 (by omega)).trans one) copyLink
  have truth:=CompilerSubgroupConstructor84.independent_source_complete TransferFirstSubgroupData01.graph
    CapturedFirstSubgroup81.d CapturedFirstSubgroup81.negative initial
    (fun input => eval (completed base initial) (TransferFirstSubgroupData01.inputTerms input)) imaginary
    (CompilerSubgroupSource80.modulus_negative_one (F:=F)) CapturedFirstSubgroup81.shape nonSquare imaginarySquare valid
  apply CompilerSubgroupConstructor84.original_from_arithmetic
    (completed base initial) (CompilerSubgroupConstructor84.completed_copy (seeded base initial) copyLink)
    (CompilerSubgroupConstructor84.completed_emitted (seeded base initial))
  intro ports member
  have equality:=truth ports member
  rw [←input_identity base initial] at equality
  exact (congrFun values ports.1).trans (equality.trans (congrFun values ports.2).symm)
theorem outside (base : Nat → F) (initial : Group.Point F) (column : Nat)
    (seedOutside : column<14 ∨ 21≤column) (arithmeticOutside : column<22738 ∨ 22802≤column) :
    completed base initial column=base column :=
  (arithmetic_outside (seeded base initial) column arithmeticOutside).trans (seeded_outside base initial column seedOutside)
end ShielddSecurity.CapturedFirstSubgroupSeed85
