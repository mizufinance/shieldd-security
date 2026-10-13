import ShielddSecurity.AuthorizationSubgroupCapture409B05Check0
import ShielddSecurity.AuthorizationSubgroupCapture409B05Check1
import ShielddSecurity.AuthorizationSubgroupCapture409B05Check2
import ShielddSecurity.AuthorizationSubgroupCapture409B05Check3
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSubgroupCapture409B05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

noncomputable def arithmeticCheck : Bool := (List.range 64).all (fun index =>
  decide (CapturedFullArithmetic52.rowAt (26978+index)=arithmeticRows[index]?))
theorem arithmetic_checked : arithmeticCheck=true := by
  apply List.all_eq_true.mpr
  intro index member
  have bound : index<64 := List.mem_range.mp member
  by_cases before0 : index<16
  · have certificate := List.all_eq_true.mp AuthorizationSubgroupCapture409B05Check0.checked (index-0) (List.mem_range.mpr (by omega))
    have position : 0+(index-0)=index := by omega
    simpa only [position] using certificate
  by_cases before1 : index<32
  · have certificate := List.all_eq_true.mp AuthorizationSubgroupCapture409B05Check1.checked (index-16) (List.mem_range.mpr (by omega))
    have position : 16+(index-16)=index := by omega
    simpa only [position] using certificate
  by_cases before2 : index<48
  · have certificate := List.all_eq_true.mp AuthorizationSubgroupCapture409B05Check2.checked (index-32) (List.mem_range.mpr (by omega))
    have position : 32+(index-32)=index := by omega
    simpa only [position] using certificate
  have certificate := List.all_eq_true.mp AuthorizationSubgroupCapture409B05Check3.checked (index-48) (List.mem_range.mpr (by omega))
  have position : 48+(index-48)=index := by omega
  simpa only [position] using certificate

theorem copy_checked : arithmeticRows[64]?=some (TransferFirstSubgroupData01.arithmeticRows[64]) := by decide +kernel

theorem length_checked : arithmeticRows.length=65 := by decide +kernel

theorem zero_fixed : rename 0=0 := by decide +kernel
theorem copy_fixed : rename copy=copy := by decide +kernel

noncomputable def assertionCheck : Bool := (List.range 6).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+1979+index)=originalRows[64+index]?))
theorem assertion_checked : assertionCheck=true := by decide +kernel

variable {F : Type} [Field F] [CharP F p]
theorem from_arithmetic (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (linked : rho copy=rho 0) :
    Satisfies rho arithmeticRows := by
  intro row member
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨before,_⟩ := List.getElem?_eq_some_iff.mp found
  rw [length_checked] at before
  by_cases arith : index<64
  · have position := of_decide_eq_true (List.all_eq_true.mp arithmetic_checked index (List.mem_range.mpr arith))
    exact sat (26978+index) (by omega) row (position.trans found)
  · have sameIndex : index=64 := by omega
    subst index
    have same := Option.some.inj (copy_checked.symm.trans found)
    subst row
    apply (CompilerAssertionBlock51.checked_iff copy _ _ CapturedSubgroupSelection87.copy_checked rho linked).mpr
    simpa [CompilerAssertionBlock51.Truth,CompilerAssertionBlock51.sourceLeft,CompilerAssertionBlock51.sourceRight,
      expressionValue,eval,CompilerArithmeticTransport41.copy,TransferFirstSubgroupData01.copy] using linked.symm

theorem pulled (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (linked : rho copy=rho 0) :
    Satisfies (fun column => rho (rename column)) TransferFirstSubgroupData01.arithmeticRows.toList :=
  (CompilerColumnRenaming05.satisfies_rows rename rho _).mp (from_arithmetic rho sat linked)

theorem complete (rho : Nat → F) (initial : Group.Point F) (imaginary : F)
    (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (roles : CapturedFourSubgroupConstructor88.InputRoles (fun column => rho (rename column)) initial)
    (valid : Group.OnCurve (CapturedFirstSubgroup81.d:F) initial)
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+1979+index)) 6 := by
  have localRows := CapturedSubgroupActual86.original_from_constructed_inputs
    (fun column => rho (rename column)) initial imaginary
    (by simpa only [zero_fixed] using zero) (by simpa only [zero_fixed,copy_fixed] using linked)
    (pulled rho arithmetic linked) (CapturedFourSubgroupConstructor88.input_identity _ _ roles)
    valid nonSquare imaginarySquare
  have fullRows : Satisfies rho originalRows :=
    (CompilerColumnRenaming05.satisfies_rows rename rho _).mpr localRows
  intro index bound row found
  have position := of_decide_eq_true (List.all_eq_true.mp assertion_checked index (List.mem_range.mpr bound))
  exact fullRows row (List.mem_iff_getElem?.mpr ⟨64+index,position.symm.trans found⟩)
end ShielddSecurity.AuthorizationSubgroupCapture409B05

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.arithmeticCheck
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.arithmeticCheck

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.arithmetic_checked
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.arithmetic_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.copy_checked
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.copy_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.length_checked
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.length_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.zero_fixed
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.zero_fixed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.copy_fixed
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.copy_fixed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.assertionCheck
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.assertionCheck

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.assertion_checked
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.from_arithmetic
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.from_arithmetic

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.pulled
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.pulled

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05.complete
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05.complete
