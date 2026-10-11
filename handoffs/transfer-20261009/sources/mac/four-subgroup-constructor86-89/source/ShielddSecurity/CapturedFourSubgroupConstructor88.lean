import ShielddSecurity.CapturedSubgroupActual86
import ShielddSecurity.CapturedSubgroupSelection87
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFourSubgroupConstructor88
open Compiler
variable {F : Type} [Field F]
def InputRoles (rho : Nat → F) (initial : Group.Point F) : Prop :=
  rho 14=(CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) initial).x ∧
  rho 15=(CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) initial).y ∧
  rho 16=initial.x ∧ rho 17=initial.y ∧
  ∀ index<3,rho (18+index)=CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) initial index
theorem input_identity (rho : Nat → F) (initial : Group.Point F) (roles : InputRoles rho initial) :
    (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input))=
    CompilerSubgroupSource80.constructedInputs (CapturedFirstSubgroup81.d:F) initial
      (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input)) := by
  have inputs (input : Nat) : eval rho (TransferFirstSubgroupData01.inputTerms input)=rho (3+input) := by
    simp [TransferFirstSubgroupData01.inputTerms,eval]
  funext input
  by_cases a:input=11
  · subst input; rw [inputs]; exact roles.1
  by_cases b:input=12
  · subst input; rw [inputs]; exact roles.2.1
  by_cases c:input=13
  · subst input; rw [inputs]; exact roles.2.2.1
  by_cases d:input=14
  · subst input; rw [inputs]; exact roles.2.2.2.1
  by_cases h:15≤input ∧ input<18
  · simp only [CompilerSubgroupSource80.constructedInputs,if_neg a,if_neg b,if_neg c,if_neg d,if_pos h,inputs]
    have same : 3+input=18+(input-15) := by omega
    rw [same]
    exact roles.2.2.2.2 (input-15) (by omega)
  · simp only [CompilerSubgroupSource80.constructedInputs,if_neg a,if_neg b,if_neg c,if_neg d,if_neg h]
theorem zero_fixed (group : Fin 4) : CapturedSubgroupSelection87.rename group 0=0 := by
  rcases group with ⟨group,bound⟩
  interval_cases group <;> rfl
theorem copy_fixed (group : Fin 4) : CapturedSubgroupSelection87.rename group TransferFirstSubgroupData01.copy=
    TransferFirstSubgroupData01.copy := by
  rcases group with ⟨group,bound⟩
  interval_cases group <;> rfl
def originalRows (group : Fin 4) : List Row := CompilerColumnRenaming05.rows
  (CapturedSubgroupSelection87.rename group) TransferFirstSubgroupData01.originalRows.toList
variable [CharP F TransferFirstSubgroupData01.p]
theorem all_four (rho : Nat → F) (initial : Fin 4 → Group.Point F) (imaginary : F)
    (one : rho 0=1) (linked : rho TransferFirstSubgroupData01.copy=rho 0)
    (arithmetic : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (roles : ∀ group,InputRoles (fun column => rho (CapturedSubgroupSelection87.rename group column)) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    ∀ group,Satisfies rho (originalRows group) := by
  intro group
  apply (CompilerColumnRenaming05.satisfies_rows (CapturedSubgroupSelection87.rename group) rho _).mpr
  apply CapturedSubgroupActual86.original_from_constructed_inputs
    (fun column => rho (CapturedSubgroupSelection87.rename group column)) (initial group) imaginary
  · simpa only [zero_fixed] using one
  · simpa only [zero_fixed,copy_fixed] using linked
  · exact CapturedSubgroupSelection87.pulled rho group arithmetic linked
  · exact input_identity _ _ (roles group)
  · exact valid group
  · exact nonSquare
  · exact imaginarySquare
end ShielddSecurity.CapturedFourSubgroupConstructor88

set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupConstructor88.InputRoles
#print axioms ShielddSecurity.CapturedFourSubgroupConstructor88.InputRoles
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupConstructor88.input_identity
#print axioms ShielddSecurity.CapturedFourSubgroupConstructor88.input_identity
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupConstructor88.zero_fixed
#print axioms ShielddSecurity.CapturedFourSubgroupConstructor88.zero_fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupConstructor88.copy_fixed
#print axioms ShielddSecurity.CapturedFourSubgroupConstructor88.copy_fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupConstructor88.originalRows
#print axioms ShielddSecurity.CapturedFourSubgroupConstructor88.originalRows
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupConstructor88.all_four
#print axioms ShielddSecurity.CapturedFourSubgroupConstructor88.all_four
