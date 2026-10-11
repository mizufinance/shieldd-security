import ShielddSecurity.CapturedAssetCanonical112
import ShielddSecurity.CapturedValueGlobal108
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAssetGlobal113
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position : Nat) : Nat → F :=
  CapturedValueGlobal108.completed (CapturedRegistryAssetRange109.completed base asset) initial value epoch position
theorem claimed_seed (base : Nat → F) (asset : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (CapturedRegistryAssetRange109.completed base asset) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [CapturedRegistryAssetRange109.completed_outside base asset _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    CapturedRegistryAssetRange109.completed_outside base asset _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]
theorem bits_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position index : Nat) (bound : index<255) :
    completed base initial asset value epoch position (471+index)=
      CapturedRegistryAssetRange109.completed base asset (471+index) := by
  have small : 471+index<22738 := by omega
  have notVerifier : 471+index≠1 ∧ 471+index≠2 ∧ 471+index≠copy := by
    have c : copy=200692 := rfl
    omega
  have notEpoch : ¬(49≤471+index ∧ 471+index<135) := by omega
  have notPosition : 216≤471+index := by omega
  have seedSmall : ∀ column∈CapturedFourSubgroupSeed89.hintColumns,column<216 := by decide
  have notSeed : 471+index∉CapturedFourSubgroupSeed89.hintColumns := by
    intro member
    have h:=seedSmall (471+index) member
    omega
  have a:=(CapturedGlobalPosition77.outside
    (CapturedFourSubgroupSeed89.seeded (CapturedRegistryValueRange97.completed (CapturedRegistryAssetRange109.completed base asset) value) initial)
    epoch position (471+index) (Or.inl small) notVerifier notEpoch (Or.inr notPosition)).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial _ notSeed)
  exact a.trans (CapturedRegistryValueRange97.completed_outside _ value (471+index) (Or.inr (by omega)))
theorem bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position index : Nat) (bound : index<255) :
    completed base initial asset value epoch position (471+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt asset (216+index)) := by
  rw [bits_frame base initial asset value epoch position index bound]
  change writeBits base 471 (encodeBits 255 asset) (471+index)=_
  unfold writeBits
  rw [if_pos (show 471≤471+index ∧ 471+index<471+(encodeBits 255 asset).length by
    rw [encodeBits_length];omega)]
  rw [Nat.add_sub_cancel_left]
  change (if (encodeBits 255 asset)[index]?.getD false then (1:F) else 0)=
    (if (encodeBits 255 asset)[216+index-216]?.getD false then 1 else 0)
  rw [Nat.add_sub_cancel_left]
theorem six_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position : Nat) : completed base initial asset value epoch position 6=base 6 :=
  (CapturedRegulatedAsset96.outside_early _ initial epoch position 6 (by decide) (by decide) (by decide)).trans
    ((CapturedRegistryValueRange97.completed_outside _ value 6 (Or.inl (by decide))).trans
      (CapturedRegistryAssetRange109.completed_fixed base asset).2.2.2.2)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position : Nat) (one : base 0=1) :
    completed base initial asset value epoch position 0=1 :=
  CapturedValueGlobal108.zero _ initial value epoch position
    ((CapturedRegistryAssetRange109.completed_fixed base asset).1.trans one)
variable [CharP F p]
theorem range_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position : Nat) (bound : asset<2^255) (meaning : base 6=(asset:F)) :
    SatisfiesAt (completed base initial asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (178377+index)) 256 := by
  have seeded:=CapturedRegistryAssetRange109.completed_truth base asset bound meaning
  have parts:=(CapturedRegistryAssetRange109.truth_iff _).mp seeded
  have truth : TruthAt (completed base initial asset value epoch position) CapturedRegistryAssetRange109.block.recipe 256 := by
    apply (CapturedRegistryAssetRange109.truth_iff _).mpr
    constructor
    · intro index before
      rw [bits_frame base initial asset value epoch position index before]
      exact parts.1 index before
    · have same : CapturedRegistryAssetRange109.columns.map (completed base initial asset value epoch position)=
          CapturedRegistryAssetRange109.columns.map (CapturedRegistryAssetRange109.completed base asset) := by
        apply List.map_congr_left
        intro column member
        change column∈List.range' 471 255 at member
        obtain ⟨index,before,equal⟩:=List.mem_range'.mp member
        simp only [one_mul] at equal
        subst column
        exact bits_frame base initial asset value epoch position index before
      rw [same,six_frame]
      exact parts.2.trans (CapturedRegistryAssetRange109.completed_fixed base asset).2.2.2.2
  have linked : completed base initial asset value epoch position copy=completed base initial asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have rows:=(satisfies_iff copy 256 CapturedRegistryAssetRange109.block _ linked).mpr truth
  intro index before row found
  change CapturedFullRelation58.rowAt (178377+index)=some row at found
  rw [CapturedRegistryAssetRange109.full_position index before] at found
  exact rows index before row found
theorem canonical_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset value epoch position : Nat) (bound : asset<p) (one : base 0=1) :
    SatisfiesAt (completed base initial asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (178633+index)) 2 := by
  have z:=zero base initial asset value epoch position one
  have linked : completed base initial asset value epoch position copy=completed base initial asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have arithmetic : SatisfiesAt (completed base initial asset value epoch position) CapturedFullArithmetic52.rowAt 177954 :=
    CapturedGlobalRegistered74.completed_arithmetic _ _
  exact CapturedAssetCanonical112.complete _ asset bound z (linked.trans z) arithmetic
    (bits base initial asset value epoch position)
theorem legal_registry_global680 (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=CapturedRegistryPointDomain75.sink)
    (base : Nat → F) (initial : Fin 4 → Group.Point F) (imaginary : F)
    (epoch : base 34=(w.registry.audit.epoch:F)) (position : base 135=(w.registry.position:F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (asset : base 6=(w.asset:F)) (registry : base 11=(w.registry.value:F))
    (px : base 35=(w.registry.audit.payload.x:F)) (py : base 36=(w.registry.audit.payload.y:F))
    (cx : base 42=(w.registry.audit.checking.x:F)) (cy : base 43=(w.registry.audit.checking.y:F))
    (zero : base 0=1)
    (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 163 ∧
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 ∧
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 ∧
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 ∧
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178377+index)) 256 ∧
    SatisfiesAt (completed base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178633+index)) 2 := by
  have low (column : Nat) (bound : column<471) : CapturedRegistryAssetRange109.completed base w.asset column=base column :=
    CapturedRegistryAssetRange109.completed_outside base _ column (Or.inl bound)
  have first:=CapturedValueGlobal108.legal_registry_global422 c w legal sinkMeaning
    (CapturedRegistryAssetRange109.completed base w.asset) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.asset group).trans (binding group))
    valid nonSquare imaginarySquare
  have assetBound : w.asset<p := legal.2.2.2.2.2.2.2.1
  exact ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,first.2.2.2.2,
    range_assertions base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position
      (Nat.lt_trans assetBound CapturedRegistryValueFrame98.modulus_bound) asset,
    canonical_assertions base initial w.asset w.registry.value w.registry.audit.epoch w.registry.position assetBound zero⟩
end ShielddSecurity.CapturedAssetGlobal113
