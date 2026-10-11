import ShielddSecurity.CapturedHighZero126
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedHighZeroShared127
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
def difference (asset value : Nat) : F := ((asset/2^128:Nat):F)-((value/2^128:Nat):F)
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : Nat → F :=
  CapturedHighLimbShared124.completed (FieldZeroSeed125.seeded base 1110 (difference asset value))
    initial next asset value epoch position
theorem early_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 981≤column) (upper : column<22738) :
    CapturedNextGlobal118.completed base initial next asset value epoch position column=base column := by
  have small : column<22738 := by omega
  have notVerifier : column≠1 ∧ column≠2 ∧ column≠copy := by
    have c : copy=200692 := rfl
    omega
  have notEpoch : ¬(49≤column ∧ column<135) := by omega
  have notPosition : 216≤column := by omega
  have seedSmall : ∀ c∈CapturedFourSubgroupSeed89.hintColumns,c<216 := by decide
  have notSeed : column∉CapturedFourSubgroupSeed89.hintColumns := by
    intro member
    have h:=seedSmall column member
    omega
  have a:=(CapturedGlobalPosition77.outside
    (CapturedFourSubgroupSeed89.seeded (CapturedRegistryValueRange97.completed
      (CapturedRegistryAssetRange109.completed (CapturedRegistryNextRange114.completed base next) asset) value) initial)
    epoch position column (Or.inl small) notVerifier notEpoch (Or.inr notPosition)).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial _ notSeed)
  exact a.trans ((CapturedRegistryValueRange97.completed_outside _ value column (Or.inr (by omega))).trans
    ((CapturedRegistryAssetRange109.completed_outside _ asset column (Or.inr (by omega))).trans
      (CapturedRegistryNextRange114.completed_outside _ next column (Or.inr (by omega)))))
theorem zero_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1110≤column) (upper : column<1112) :
    completed base initial next asset value epoch position column=
      FieldZeroSeed125.seeded base 1110 (difference asset value) column := by
  exact (early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    (CapturedRegistryHighLimb121.outside _ (asset/2^128) (value/2^128) column (Or.inr lower))
theorem claimed_seed (base : Nat → F) (asset value : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (FieldZeroSeed125.seeded base 1110 (difference asset value)) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [FieldZeroSeed125.outside base _ _ _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    FieldZeroSeed125.outside base _ _ _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]
theorem meaning (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (left : asset<2^255) (right : value<2^255) :
    eval (completed base initial next asset value epoch position) CapturedHighZero126.delta=difference asset value := by
  unfold CapturedHighZero126.delta
  rw [eval_append,weighted_eval,weighted_eval]
  rw [CapturedHighLimbGlobal123.asset_high _ initial next asset value epoch position left,
    CapturedHighLimbGlobal123.value_high _ initial next asset value epoch position right]
  simp only [difference,Int.cast_one,Int.cast_neg,one_mul,neg_mul,sub_eq_add_neg]
  ring
variable [CharP F p]
theorem zero_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (left : asset<2^255) (right : value<2^255) (one : base 0=1) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (179023+index)) 3 := by
  apply CapturedHighZero126.complete _ (difference asset value)
  · exact CapturedGlobalRegistered74.completed_arithmetic _ _
  · exact meaning base initial next asset value epoch position left right
  · exact (zero_frame base initial next asset value epoch position 1110 (by decide) (by decide)).trans
      (FieldZeroSeed125.flag_value base _ _)
  · exact (zero_frame base initial next asset value epoch position 1111 (by decide) (by decide)).trans
      (FieldZeroSeed125.inverse_value base _ _)
  · exact CapturedHighLimbGlobal123.zero _ initial next asset value epoch position
      ((FieldZeroSeed125.outside base _ _ 0 (Or.inl (by decide))).trans one)
  · exact CapturedGlobalRegistered74.completed_copy _ _
theorem legal_registry_global1071 (c : TransferSem.Crypto) (w : TransferSem.Witness)
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
    ((SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
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
      (fun index => CapturedFullRelation58.rowAt (178891+index)) 2) ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178893+index)) 130) ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179023+index)) 3 := by
  have low (column : Nat) (bound : column<1110) :
      FieldZeroSeed125.seeded base 1110 (difference w.asset w.registry.value) column=base column :=
    FieldZeroSeed125.outside base _ _ column (Or.inl bound)
  have first:=CapturedHighLimbShared124.legal_registry_global1068 c w legal sinkMeaning
    (FieldZeroSeed125.seeded base 1110 (difference w.asset w.registry.value)) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 13 (by decide)).trans nextMeaning) ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.asset w.registry.value group).trans (binding group))
    valid nonSquare imaginarySquare
  exact ⟨first,zero_assertions base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position
    (Nat.lt_trans legal.2.2.2.2.2.2.2.1 CapturedRegistryValueFrame98.modulus_bound)
    (Nat.lt_trans legal.2.2.2.2.2.2.1 CapturedRegistryValueFrame98.modulus_bound) zero⟩
end ShielddSecurity.CapturedHighZeroShared127
