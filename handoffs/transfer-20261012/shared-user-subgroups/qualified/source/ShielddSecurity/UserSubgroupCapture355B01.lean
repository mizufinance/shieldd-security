import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserSubgroupCapture355B01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def rename (column : Nat) : Nat :=
  if 14≤column ∧ column<21 then 1512+(column-14)
  else if 22738≤column ∧ column<22802 then 33874+(column-22738)
  else column

def arithmeticRows : List Row :=
  CompilerColumnRenaming05.rows rename TransferFirstSubgroupData01.arithmeticRows.toList

def originalRows : List Row :=
  CompilerColumnRenaming05.rows rename TransferFirstSubgroupData01.originalRows.toList

noncomputable def arithmeticCheck : Bool := (List.range 64).all (fun index =>
  decide (CapturedFullArithmetic52.rowAt (11136+index)=arithmeticRows[index]?))
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel

theorem copy_checked : arithmeticRows[64]?=some (TransferFirstSubgroupData01.arithmeticRows[64]) := by decide +kernel

theorem length_checked : arithmeticRows.length=65 := by decide +kernel

theorem zero_fixed : rename 0=0 := by decide +kernel
theorem copy_fixed : rename copy=copy := by decide +kernel

noncomputable def assertionCheck : Bool := (List.range 6).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+1476+index)=originalRows[64+index]?))
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
    exact sat (11136+index) (by omega) row (position.trans found)
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
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+1476+index)) 6 := by
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
end ShielddSecurity.UserSubgroupCapture355B01

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.rename
#print axioms ShielddSecurity.UserSubgroupCapture355B01.rename

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.arithmeticRows
#print axioms ShielddSecurity.UserSubgroupCapture355B01.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.originalRows
#print axioms ShielddSecurity.UserSubgroupCapture355B01.originalRows

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.arithmeticCheck
#print axioms ShielddSecurity.UserSubgroupCapture355B01.arithmeticCheck

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.arithmetic_checked
#print axioms ShielddSecurity.UserSubgroupCapture355B01.arithmetic_checked

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.copy_checked
#print axioms ShielddSecurity.UserSubgroupCapture355B01.copy_checked

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.length_checked
#print axioms ShielddSecurity.UserSubgroupCapture355B01.length_checked

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.zero_fixed
#print axioms ShielddSecurity.UserSubgroupCapture355B01.zero_fixed

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.copy_fixed
#print axioms ShielddSecurity.UserSubgroupCapture355B01.copy_fixed

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.assertionCheck
#print axioms ShielddSecurity.UserSubgroupCapture355B01.assertionCheck

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.assertion_checked
#print axioms ShielddSecurity.UserSubgroupCapture355B01.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.from_arithmetic
#print axioms ShielddSecurity.UserSubgroupCapture355B01.from_arithmetic

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.pulled
#print axioms ShielddSecurity.UserSubgroupCapture355B01.pulled

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B01.complete
#print axioms ShielddSecurity.UserSubgroupCapture355B01.complete
