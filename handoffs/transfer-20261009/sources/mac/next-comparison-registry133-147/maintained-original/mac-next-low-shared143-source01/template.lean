import ShielddSecurity.CapturedNextLowGlobal142
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextLowShared143
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed := CapturedNextLowGlobal142.completed (F:=F)
theorem claimed_seed (base : Nat → F) (next asset : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (CapturedNextLowLimb141.seeded base (LowBitMeaning128.low next) (LowBitMeaning128.low asset)) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [CapturedNextLowLimb141.outside base _ _ _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    CapturedNextLowLimb141.outside base _ _ _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]
variable [CharP F p]
theorem legal_registry_global1466 (c : TransferSem.Crypto) (w : TransferSem.Witness)
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
    ((((((SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
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
      (fun index => CapturedFullRelation58.rowAt (179023+index)) 3) ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179026+index)) 131) ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179157+index)) 130) ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179287+index)) 3) ∧
    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (179290+index)) 131 := by
  have low (column : Nat) (bound : column<1373) :
      CapturedNextLowLimb141.seeded base (LowBitMeaning128.low w.registry.nextValue) (LowBitMeaning128.low w.asset) column=base column :=
    CapturedNextLowLimb141.outside base _ _ column (Or.inl bound)
  have first:=CapturedNextHighZeroShared139.legal_registry_global1335 c w legal sinkMeaning
    (CapturedNextLowLimb141.seeded base (LowBitMeaning128.low w.registry.nextValue) (LowBitMeaning128.low w.asset)) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 13 (by decide)).trans nextMeaning) ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.registry.nextValue w.asset group).trans (binding group))
    valid nonSquare imaginarySquare
  exact ⟨first,CapturedNextLowGlobal142.low_assertions base initial
    w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position⟩
end ShielddSecurity.CapturedNextLowShared143
