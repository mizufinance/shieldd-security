import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupPosition91
open Compiler CompilerAssertionBlock51
noncomputable def selectionCheck (group : Fin 4) : Bool :=
  (List.range 6).all (fun index => decide (CapturedSubgroupSelection87.fullPosition group (64+index)=177955+group.val*6+index))
theorem selection_checked0 : selectionCheck ⟨0,by decide⟩=true := by rfl
theorem selection_checked1 : selectionCheck ⟨1,by decide⟩=true := by rfl
theorem selection_checked2 : selectionCheck ⟨2,by decide⟩=true := by rfl
theorem selection_checked3 : selectionCheck ⟨3,by decide⟩=true := by rfl
theorem selection_checked (group : Fin 4) : selectionCheck group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact selection_checked0
  · exact selection_checked1
  · exact selection_checked2
  · exact selection_checked3
variable {F : Type} [Field F]
theorem full_rows (rho : Nat → F)
    (rows : ∀ group,Satisfies rho (CapturedFourSubgroupConstructor88.originalRows group)) :
    ∀ group,Satisfies rho (CapturedSubgroupSelection87.fullRows group) := by
  intro group
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact (CompilerColumnRenaming05.satisfies_rows id rho _).mp (rows ⟨0,by decide⟩)
  · exact rows ⟨1,by decide⟩
  · exact rows ⟨2,by decide⟩
  · exact rows ⟨3,by decide⟩
theorem subgroup_positions (rho : Nat → F)
    (rows : ∀ group,Satisfies rho (CapturedFourSubgroupConstructor88.originalRows group)) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177955+index)) 24 := by
  intro index bound row found
  let group : Fin 4:=⟨index/6,by omega⟩
  let localIndex := index%6
  have small : localIndex<6 := Nat.mod_lt _ (by decide)
  have checked:=selection_checked group
  have length:=of_decide_eq_true (Bool.and_eq_true_iff.mp (CapturedSubgroupSelection87.checked group)).2
  have position:=of_decide_eq_true (List.all_eq_true.mp checked localIndex (List.mem_range.mpr small))
  have exactBody:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp (CapturedSubgroupSelection87.full_checked group)
    (64+localIndex) (List.mem_range.mpr (by omega)))
  have body:=of_decide_eq_true exactBody.2
  have eqIndex : 177955+group.val*6+localIndex=177955+index := by
    dsimp [group,localIndex]
    omega
  rw [position,eqIndex] at body
  have present : row∈CapturedSubgroupSelection87.fullRows group :=
    List.mem_iff_getElem?.mpr ⟨64+localIndex,body.symm.trans found⟩
  exact full_rows rho rows group row present
end ShielddSecurity.CapturedSubgroupPosition91

set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.selectionCheck
#print axioms ShielddSecurity.CapturedSubgroupPosition91.selectionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.selection_checked0
#print axioms ShielddSecurity.CapturedSubgroupPosition91.selection_checked0
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.selection_checked1
#print axioms ShielddSecurity.CapturedSubgroupPosition91.selection_checked1
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.selection_checked2
#print axioms ShielddSecurity.CapturedSubgroupPosition91.selection_checked2
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.selection_checked3
#print axioms ShielddSecurity.CapturedSubgroupPosition91.selection_checked3
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.selection_checked
#print axioms ShielddSecurity.CapturedSubgroupPosition91.selection_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.full_rows
#print axioms ShielddSecurity.CapturedSubgroupPosition91.full_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupPosition91.subgroup_positions
#print axioms ShielddSecurity.CapturedSubgroupPosition91.subgroup_positions
