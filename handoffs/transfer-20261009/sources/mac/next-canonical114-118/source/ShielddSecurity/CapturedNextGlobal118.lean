import ShielddSecurity.CapturedNextCanonical117
import ShielddSecurity.CapturedAssetGlobal113
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextGlobal118
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : Nat → F :=
  CapturedAssetGlobal113.completed (CapturedRegistryNextRange114.completed base next) initial asset value epoch position
theorem claimed_seed (base : Nat → F) (next : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (CapturedRegistryNextRange114.completed base next) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [CapturedRegistryNextRange114.completed_outside base next _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    CapturedRegistryNextRange114.completed_outside base next _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]
theorem bits_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (726+index)=
      CapturedRegistryNextRange114.completed base next (726+index) := by
  have small : 726+index<22738 := by omega
  have notVerifier : 726+index≠1 ∧ 726+index≠2 ∧ 726+index≠copy := by
    have c : copy=200692 := rfl
    omega
  have notEpoch : ¬(49≤726+index ∧ 726+index<135) := by omega
  have notPosition : 216≤726+index := by omega
  have seedSmall : ∀ column∈CapturedFourSubgroupSeed89.hintColumns,column<216 := by decide
  have notSeed : 726+index∉CapturedFourSubgroupSeed89.hintColumns := by
    intro member
    have h:=seedSmall (726+index) member
    omega
  have a:=(CapturedGlobalPosition77.outside
    (CapturedFourSubgroupSeed89.seeded (CapturedRegistryValueRange97.completed (CapturedRegistryAssetRange109.completed (CapturedRegistryNextRange114.completed base next) asset) value) initial)
    epoch position (726+index) (Or.inl small) notVerifier notEpoch (Or.inr notPosition)).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial _ notSeed)
  exact a.trans ((CapturedRegistryValueRange97.completed_outside _ value (726+index) (Or.inr (by omega))).trans
    (CapturedRegistryAssetRange109.completed_outside _ asset (726+index) (Or.inr (by omega))))
theorem bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (726+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt next (216+index)) := by
  rw [bits_frame base initial next asset value epoch position index bound]
  change writeBits base 726 (encodeBits 255 next) (726+index)=_
  unfold writeBits
  rw [if_pos (show 726≤726+index ∧ 726+index<726+(encodeBits 255 next).length by
    rw [encodeBits_length];omega)]
  rw [Nat.add_sub_cancel_left]
  change (if (encodeBits 255 next)[index]?.getD false then (1:F) else 0)=
    (if (encodeBits 255 next)[216+index-216]?.getD false then 1 else 0)
  rw [Nat.add_sub_cancel_left]
theorem thirteen_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : completed base initial next asset value epoch position 13=base 13 :=
  (CapturedRegulatedAsset96.outside_early _ initial epoch position 13 (by decide) (by decide) (by decide)).trans
    ((CapturedRegistryValueRange97.completed_outside _ value 13 (Or.inl (by decide))).trans
      ((CapturedRegistryAssetRange109.completed_outside _ asset 13 (Or.inl (by decide))).trans
        (CapturedRegistryNextRange114.completed_fixed base next).2.2.2.2))
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedAssetGlobal113.zero _ initial asset value epoch position
    ((CapturedRegistryNextRange114.completed_fixed base next).1.trans one)
variable [CharP F p]
theorem range_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : next<2^255) (meaning : base 13=(next:F)) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (178635+index)) 256 := by
  have seeded:=CapturedRegistryNextRange114.completed_truth base next bound meaning
  have parts:=(CapturedRegistryNextRange114.truth_iff _).mp seeded
  have truth : TruthAt (completed base initial next asset value epoch position) CapturedRegistryNextRange114.block.recipe 256 := by
    apply (CapturedRegistryNextRange114.truth_iff _).mpr
    constructor
    · intro index before
      rw [bits_frame base initial next asset value epoch position index before]
      exact parts.1 index before
    · have same : CapturedRegistryNextRange114.columns.map (completed base initial next asset value epoch position)=
          CapturedRegistryNextRange114.columns.map (CapturedRegistryNextRange114.completed base next) := by
        apply List.map_congr_left
        intro column member
        change column∈List.range' 726 255 at member
        obtain ⟨index,before,equal⟩:=List.mem_range'.mp member
        simp only [one_mul] at equal
        subst column
        exact bits_frame base initial next asset value epoch position index before
      rw [same,thirteen_frame]
      exact parts.2.trans (CapturedRegistryNextRange114.completed_fixed base next).2.2.2.2
  have linked : completed base initial next asset value epoch position copy=completed base initial next asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have rows:=(satisfies_iff copy 256 CapturedRegistryNextRange114.block _ linked).mpr truth
  intro index before row found
  change CapturedFullRelation58.rowAt (178635+index)=some row at found
  rw [CapturedRegistryNextRange114.full_position index before] at found
  exact rows index before row found
theorem canonical_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : next<p) (one : base 0=1) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (178891+index)) 2 := by
  have z:=zero base initial next asset value epoch position one
  have linked : completed base initial next asset value epoch position copy=completed base initial next asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have arithmetic : SatisfiesAt (completed base initial next asset value epoch position) CapturedFullArithmetic52.rowAt 177954 :=
    CapturedGlobalRegistered74.completed_arithmetic _ _
  exact CapturedNextCanonical117.complete _ next bound z (linked.trans z) arithmetic
    (bits base initial next asset value epoch position)
theorem legal_registry_global938 (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (sinkMeaning : c.unregulatedRing=CapturedRegistryPointDomain75.sink)
    (base : Nat → F) (initial : Fin 4 → Group.Point F) (imaginary : F)
    (epoch : base 34=(w.registry.audit.epoch:F)) (position : base 135=(w.registry.position:F))
    (regulated : base 10=(if w.regulated then 1 else 0))
    (asset : base 6=(w.asset:F)) (registry : base 11=(w.registry.value:F))
    (px : base 35=(w.registry.audit.payload.x:F)) (py : base 36=(w.registry.audit.payload.y:F))
    (cx : base 42=(w.registry.audit.checking.x:F)) (cy : base 43=(w.registry.audit.checking.y:F))
    (nextMeaning : base 13=(w.registry.nextValue:F))
    (zero : base 0=1)
    (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 163 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178377+index)) 256 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178633+index)) 2 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178635+index)) 256 ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178891+index)) 2 := by
  have low (column : Nat) (bound : column<726) : CapturedRegistryNextRange114.completed base w.registry.nextValue column=base column :=
    CapturedRegistryNextRange114.completed_outside base _ column (Or.inl bound)
  have first:=CapturedAssetGlobal113.legal_registry_global680 c w legal sinkMeaning
    (CapturedRegistryNextRange114.completed base w.registry.nextValue) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.registry.nextValue group).trans (binding group))
    valid nonSquare imaginarySquare
  have nextBound : w.registry.nextValue<p := legal.2.2.2.2.2.2.2.2.1
  exact ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,first.2.2.2.2.1,first.2.2.2.2.2.1,first.2.2.2.2.2.2,
    range_assertions base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position
      (Nat.lt_trans nextBound CapturedRegistryValueFrame98.modulus_bound) nextMeaning,
    canonical_assertions base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position nextBound zero⟩
end ShielddSecurity.CapturedNextGlobal118

set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.completed
#print axioms ShielddSecurity.CapturedNextGlobal118.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.claimed_seed
#print axioms ShielddSecurity.CapturedNextGlobal118.claimed_seed
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.bits_frame
#print axioms ShielddSecurity.CapturedNextGlobal118.bits_frame
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.bits
#print axioms ShielddSecurity.CapturedNextGlobal118.bits
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.thirteen_frame
#print axioms ShielddSecurity.CapturedNextGlobal118.thirteen_frame
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.zero
#print axioms ShielddSecurity.CapturedNextGlobal118.zero
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.range_assertions
#print axioms ShielddSecurity.CapturedNextGlobal118.range_assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.canonical_assertions
#print axioms ShielddSecurity.CapturedNextGlobal118.canonical_assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedNextGlobal118.legal_registry_global938
#print axioms ShielddSecurity.CapturedNextGlobal118.legal_registry_global938
