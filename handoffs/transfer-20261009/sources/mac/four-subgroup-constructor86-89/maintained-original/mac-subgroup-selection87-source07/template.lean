import ShielddSecurity.CapturedFourSubgroups82
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupSelection87
open Compiler
def rename (group : Fin 4) : Nat → Nat :=
  if before : group.val=0 then id else CapturedFourSubgroups82.rename ⟨group.val-1,by omega⟩
def arithmeticRows (group : Fin 4) : List Row :=
  CompilerColumnRenaming05.rows (rename group) TransferFirstSubgroupData01.arithmeticRows.toList
def fullRows (group : Fin 4) : List Row :=
  if before : group.val=0 then CapturedFirstSubgroup81.rows else CapturedFourSubgroups82.rows ⟨group.val-1,by omega⟩
def fullPosition (group : Fin 4) (index : Nat) : Nat :=
  if before : group.val=0 then CapturedFirstSubgroup81.positions[index]! else CapturedFourSubgroups82.position ⟨group.val-1,by omega⟩ index
noncomputable def fullCheck (group : Fin 4) : Bool :=
  (List.range (fullRows group).length).all (fun index =>
    decide (fullPosition group index<200770) &&
    decide (CapturedFullRelation58.rowAt (fullPosition group index)=(fullRows group)[index]?))
theorem full_checked (group : Fin 4) : fullCheck group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact CapturedFirstSubgroup81.positions_checked
  · exact CapturedFourSubgroups82.checked ⟨0,by decide⟩
  · exact CapturedFourSubgroups82.checked ⟨1,by decide⟩
  · exact CapturedFourSubgroups82.checked ⟨2,by decide⟩
-- Only small local arrays are reduced; the accepted full-parent position proofs are reused.
noncomputable def check (group : Fin 4) : Bool :=
  (List.range 64).all (fun index => decide ((arithmeticRows group)[index]?=(fullRows group)[index]?) &&
    decide (fullPosition group index=group.val*64+index)) &&
  decide ((arithmeticRows group)[64]?=some (TransferFirstSubgroupData01.arithmeticRows[64])) &&
  decide ((arithmeticRows group).length=65) && decide ((fullRows group).length=71)
theorem checked0 : check ⟨0,by decide⟩=true := by decide +kernel
theorem checked1 : check ⟨1,by decide⟩=true := by decide +kernel
theorem checked2 : check ⟨2,by decide⟩=true := by decide +kernel
theorem checked3 : check ⟨3,by decide⟩=true := by decide +kernel
theorem checked (group : Fin 4) : check group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
theorem copy_checked : CompilerAssertionBlock51.checkRow TransferFirstSubgroupData01.p
    TransferFirstSubgroupData01.copy (TransferFirstSubgroupData01.arithmeticRows[64])
    (false,.linear [(0,1)] [(TransferFirstSubgroupData01.copy,1)])=true := by decide +kernel
variable {F : Type} [Field F] [CharP F TransferFirstSubgroupData01.p]
theorem from_arithmetic (rho : Nat → F) (group : Fin 4)
    (sat : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (linked : rho TransferFirstSubgroupData01.copy=rho 0) : Satisfies rho (arithmeticRows group) := by
  have lengths:=Bool.and_eq_true_iff.mp (checked group)
  have fullLength:=of_decide_eq_true lengths.2
  have checks:=Bool.and_eq_true_iff.mp lengths.1
  have data:=Bool.and_eq_true_iff.mp checks.1
  have length:=of_decide_eq_true checks.2
  intro row member
  obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
  obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
  have bound : index<65 := by omega
  by_cases arithmetic:index<64
  · have localChecked:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp data.1 index (List.mem_range.mpr arithmetic))
    have subset:=of_decide_eq_true localChecked.1
    have position:=of_decide_eq_true localChecked.2
    have exactChecked:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp (full_checked group) index
      (List.mem_range.mpr (by omega)))
    have body:=of_decide_eq_true exactChecked.2
    have original:=body.trans (subset.symm.trans found)
    rw [position,CapturedFullRelation58.arithmetic_position _ (by omega)] at original
    exact sat (group.val*64+index) (by omega) row original
  · have eqIndex:index=64 := by omega
    subst index
    have same:=Option.some.inj ((of_decide_eq_true data.2).symm.trans found)
    subst row
    rw [←same]
    apply (CompilerAssertionBlock51.checked_iff TransferFirstSubgroupData01.copy _ _ copy_checked rho linked).mpr
    simp [CompilerAssertionBlock51.Truth,CompilerAssertionBlock51.sourceLeft,CompilerAssertionBlock51.sourceRight,
      expressionValue,eval,linked]
theorem pulled (rho : Nat → F) (group : Fin 4)
    (sat : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (linked : rho TransferFirstSubgroupData01.copy=rho 0) :
    Satisfies (fun column => rho (rename group column)) TransferFirstSubgroupData01.arithmeticRows.toList :=
  (CompilerColumnRenaming05.satisfies_rows (rename group) rho _).mp (from_arithmetic rho group sat linked)
end ShielddSecurity.CapturedSubgroupSelection87
