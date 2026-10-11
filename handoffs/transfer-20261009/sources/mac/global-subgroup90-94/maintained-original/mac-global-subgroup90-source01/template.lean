import ShielddSecurity.CapturedFourSubgroupSeed89
import ShielddSecurity.CapturedGlobalPosition77
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGlobalSubgroup90
open Compiler CompilerAssertionBlock51
noncomputable def selectionCheck (group : Fin 4) : Bool :=
  decide (CapturedFourSubgroupConstructor88.originalRows group=CapturedSubgroupSelection87.fullRows group) &&
  decide ((CapturedSubgroupSelection87.fullRows group).length=71) &&
  (List.range 6).all (fun index => decide (CapturedSubgroupSelection87.fullPosition group (64+index)=177955+group.val*6+index))
theorem selection_checked0 : selectionCheck ⟨0,by decide⟩=true := by decide +kernel
theorem selection_checked1 : selectionCheck ⟨1,by decide⟩=true := by decide +kernel
theorem selection_checked2 : selectionCheck ⟨2,by decide⟩=true := by decide +kernel
theorem selection_checked3 : selectionCheck ⟨3,by decide⟩=true := by decide +kernel
theorem selection_checked (group : Fin 4) : selectionCheck group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact selection_checked0
  · exact selection_checked1
  · exact selection_checked2
  · exact selection_checked3
variable {F : Type} [Field F]
theorem subgroup_positions (rho : Nat → F)
    (rows : ∀ group,Satisfies rho (CapturedFourSubgroupConstructor88.originalRows group)) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177955+index)) 24 := by
  intro index bound row found
  let group : Fin 4:=⟨index/6,by omega⟩
  let localIndex := index%6
  have small : localIndex<6 := Nat.mod_lt _ (by decide)
  have checked:=Bool.and_eq_true_iff.mp (selection_checked group)
  have prefix:=Bool.and_eq_true_iff.mp checked.1
  have same:=of_decide_eq_true prefix.1
  have length:=of_decide_eq_true prefix.2
  have position:=of_decide_eq_true (List.all_eq_true.mp checked.2 localIndex (List.mem_range.mpr small))
  have exactBody:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp (CapturedSubgroupSelection87.full_checked group)
    (64+localIndex) (List.mem_range.mpr (by omega)))
  have body:=of_decide_eq_true exactBody.2
  have eqIndex : 177955+group.val*6+localIndex=177955+index := by
    dsimp [group,localIndex]
    omega
  rw [position,eqIndex] at body
  have present : row∈CapturedSubgroupSelection87.fullRows group :=
    List.mem_iff_getElem?.mpr ⟨64+localIndex,body.symm.trans found⟩
  exact rows group row (same.symm ▸ present)
def completed (base : Nat → F) (initial : Fin 4 → Group.Point F) (epoch position : Nat) : Nat → F :=
  CapturedGlobalPosition77.completed (CapturedFourSubgroupSeed89.seeded base initial) epoch position
theorem roles (base : Nat → F) (initial : Fin 4 → Group.Point F) (epoch position : Nat)
    (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group)) :
    ∀ group,CapturedFourSubgroupConstructor88.InputRoles
      (fun column => completed base initial epoch position (CapturedSubgroupSelection87.rename group column)) (initial group) := by
  intro group
  have original:=CapturedFourSubgroupSeed89.seeded_roles base initial group (binding group)
  have fixed (index : Nat) (lower : 14≤index) (upper : index≤20) :
      completed base initial epoch position (CapturedSubgroupSelection87.rename group index)=
      CapturedFourSubgroupSeed89.seeded base initial (CapturedSubgroupSelection87.rename group index) := by
    apply CapturedGlobalPosition77.outside
    all_goals
      rcases group with ⟨group,bound⟩
      interval_cases index <;> interval_cases group <;>
        norm_num [CapturedSubgroupSelection87.rename,CapturedFourSubgroups82.rename,CompilerWindowRenaming05.swap,CompilerAssertionBlock51.copy]
  refine ⟨(fixed 14 (by omega) (by omega)).trans original.1,(fixed 15 (by omega) (by omega)).trans original.2.1,
    (fixed 16 (by omega) (by omega)).trans original.2.2.1,(fixed 17 (by omega) (by omega)).trans original.2.2.2.1,?_⟩
  intro index before
  exact (fixed (18+index) (by omega) (by omega)).trans (original.2.2.2.2 index before)
variable [CharP F p]
theorem legal_registry_global163 (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=CapturedRegistryPointDomain75.sink)
    (base : Nat → F) (initial : Fin 4 → Group.Point F) (imaginary : F)
    (epoch : base 34=(w.registry.audit.epoch:F)) (position : base 135=(w.registry.position:F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (px : base 35=(w.registry.audit.payload.x:F)) (py : base 36=(w.registry.audit.payload.y:F))
    (cx : base 42=(w.registry.audit.checking.x:F)) (cy : base 43=(w.registry.audit.checking.y:F))
    (zero : base 0=1)
    (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    SatisfiesAt (completed base initial w.registry.audit.epoch w.registry.position) CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (completed base initial w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 163 := by
  have unseeded (column : Nat) (outside : column∉CapturedFourSubgroupSeed89.hintColumns) :
      CapturedFourSubgroupSeed89.seeded base initial column=base column :=
    CapturedFourSubgroupSeed89.seeded_outside base initial column outside
  have first:=CapturedGlobalPosition77.legal_registry_global139 c w legal sinkMeaning
    (CapturedFourSubgroupSeed89.seeded base initial)
    ((unseeded 34 (by decide)).trans epoch) ((unseeded 135 (by decide)).trans position)
    ((unseeded 10 (by decide)).trans regulated)
    ((unseeded 35 (by decide)).trans px) ((unseeded 36 (by decide)).trans py)
    ((unseeded 42 (by decide)).trans cx) ((unseeded 43 (by decide)).trans cy)
    ((unseeded 0 (by decide)).trans zero)
  have one : completed base initial w.registry.audit.epoch w.registry.position 0=1 :=
    CapturedGlobalRegistered74.completed_zero _ _
      ((MerkleBits29.seed_outside _ _ 0 (by decide)).trans ((unseeded 0 (by decide)).trans zero))
  have linked : completed base initial w.registry.audit.epoch w.registry.position TransferFirstSubgroupData01.copy=
      completed base initial w.registry.audit.epoch w.registry.position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have subgroup:=subgroup_positions _ (CapturedFourSubgroupConstructor88.all_four
    (completed base initial w.registry.audit.epoch w.registry.position) initial imaginary one linked first.1
    (roles base initial _ _ binding) valid nonSquare imaginarySquare)
  refine ⟨first.1,?_⟩
  intro index bound row found
  change CapturedFullRelation58.rowAt (177954+index)=some row at found
  by_cases start : index<1
  · exact first.2.2.1 index start row found
  · by_cases point : index<25
    · have same : 177954+index=177955+(index-1) := by omega
      rw [same] at found
      exact subgroup (index-1) (by omega) row found
    · by_cases epochRows : index<129
      · have same : 177954+index=177979+(index-25) := by omega
        rw [same] at found
        exact first.2.1 (index-25) (by omega) row found
      · have same : 177954+index=178083+(index-129) := by omega
        rw [same] at found
        exact first.2.2.2 (index-129) (by omega) row found
end ShielddSecurity.CapturedGlobalSubgroup90
