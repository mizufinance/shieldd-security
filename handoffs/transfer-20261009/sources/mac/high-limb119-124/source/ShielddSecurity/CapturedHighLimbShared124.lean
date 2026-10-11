import ShielddSecurity.CapturedHighLimbGlobal123
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedHighLimbShared124
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed := CapturedHighLimbGlobal123.completed (F:=F)
theorem claimed_seed (base : Nat → F) (asset value : Nat) (group : Fin 4) :
    CapturedFourSubgroupSeed89.Claimed (CapturedRegistryHighLimb121.seeded base (asset/2^128) (value/2^128)) group=
      CapturedFourSubgroupSeed89.Claimed base group := by
  have fourteen:=CapturedSubgroupFrame92.safe group 14 (by decide) (by decide)
  have fifteen:=CapturedSubgroupFrame92.safe group 15 (by decide) (by decide)
  change Group.Point.mk _ _=Group.Point.mk _ _
  rw [CapturedRegistryHighLimb121.outside base _ _ _ (Or.inl (Nat.lt_trans fourteen.2.2.2.2.2 (by decide))),
    CapturedRegistryHighLimb121.outside base _ _ _ (Or.inl (Nat.lt_trans fifteen.2.2.2.2.2 (by decide)))]
variable [CharP F p]
theorem legal_registry_global1068 (c : TransferSem.Crypto) (w : TransferSem.Witness)
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
    (SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)
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
      (fun index => CapturedFullRelation58.rowAt (178893+index)) 130 := by
  have low (column : Nat) (bound : column<981) :
      CapturedRegistryHighLimb121.seeded base (w.asset/2^128) (w.registry.value/2^128) column=base column :=
    CapturedRegistryHighLimb121.outside base _ _ column (Or.inl bound)
  have first:=CapturedNextGlobal118.legal_registry_global938 c w legal sinkMeaning
    (CapturedRegistryHighLimb121.seeded base (w.asset/2^128) (w.registry.value/2^128)) initial imaginary
    ((low 34 (by decide)).trans epoch) ((low 135 (by decide)).trans position)
    ((low 10 (by decide)).trans regulated) ((low 6 (by decide)).trans asset)
    ((low 11 (by decide)).trans registry)
    ((low 35 (by decide)).trans px) ((low 36 (by decide)).trans py)
    ((low 42 (by decide)).trans cx) ((low 43 (by decide)).trans cy)
    ((low 13 (by decide)).trans nextMeaning) ((low 0 (by decide)).trans zero)
    (fun group => (claimed_seed base w.asset w.registry.value group).trans (binding group))
    valid nonSquare imaginarySquare
  exact ⟨first,CapturedHighLimbGlobal123.high_assertions base initial
    w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position
    (Nat.lt_trans legal.2.2.2.2.2.2.2.1 CapturedRegistryValueFrame98.modulus_bound)
    (Nat.lt_trans legal.2.2.2.2.2.2.1 CapturedRegistryValueFrame98.modulus_bound)⟩
end ShielddSecurity.CapturedHighLimbShared124

set_option pp.all true in
#check @ShielddSecurity.CapturedHighLimbShared124.completed
#print axioms ShielddSecurity.CapturedHighLimbShared124.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedHighLimbShared124.claimed_seed
#print axioms ShielddSecurity.CapturedHighLimbShared124.claimed_seed
set_option pp.all true in
#check @ShielddSecurity.CapturedHighLimbShared124.legal_registry_global1068
#print axioms ShielddSecurity.CapturedHighLimbShared124.legal_registry_global1068
