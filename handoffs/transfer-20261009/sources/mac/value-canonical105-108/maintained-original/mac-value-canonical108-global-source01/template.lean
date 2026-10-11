import ShielddSecurity.CapturedValueCanonical107
import ShielddSecurity.CapturedRegistryValueGlobal99
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueGlobal108
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed := CapturedRegistryValueFrame98.completed (F:=F)
theorem bits (base : Nat → F) (initial : Fin 4 → Group.Point F) (n epoch position index : Nat)
    (bound : index<255) : completed base initial n epoch position (216+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index)) := by
  rw [CapturedRegistryValueFrame98.bits_frame base initial n epoch position index bound]
  change writeBits base 216 (encodeBits 255 n) (216+index)=_
  unfold writeBits
  rw [if_pos (show 216≤216+index ∧ 216+index<216+(encodeBits 255 n).length by
    rw [encodeBits_length];omega)]
  rfl
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F) (n epoch position : Nat)
    (one : base 0=1) : completed base initial n epoch position 0=1 := by
  apply CapturedGlobalRegistered74.completed_zero
  have a:=MerkleBits29.seed_outside (CapturedFourSubgroupSeed89.seeded (CapturedRegistryValueRange97.completed base n) initial) position 0 (Or.inl (by decide))
  have b:=CapturedFourSubgroupSeed89.seeded_outside (CapturedRegistryValueRange97.completed base n) initial 0 (by decide)
  have c:=CapturedRegistryValueRange97.completed_outside base n 0 (Or.inl (by decide))
  exact a.trans (b.trans (c.trans one))
theorem canonical_assertions [CharP F p] (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (n epoch position : Nat) (bound : n<p) (one : base 0=1) :
    SatisfiesAt (completed base initial n epoch position)
      (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 := by
  have z:=zero base initial n epoch position one
  have linked : completed base initial n epoch position copy=completed base initial n epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have arithmetic : SatisfiesAt (completed base initial n epoch position) CapturedFullArithmetic52.rowAt 177954 :=
    CapturedGlobalRegistered74.completed_arithmetic _ _
  exact CapturedValueCanonical107.complete _ n bound z (linked.trans z) arithmetic
    (bits base initial n epoch position)
theorem legal_registry_global422 [CharP F p] (c : TransferSem.Crypto) (w : TransferSem.Witness)
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
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (177954+index)) 163 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 ∧
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178375+index)) 2 := by
  have first:=CapturedRegistryValueGlobal99.legal_registry_global420 c w legal sinkMeaning base initial imaginary
    epoch position regulated asset registry px py cx cy zero binding valid nonSquare imaginarySquare
  exact ⟨first.1,first.2.1,first.2.2.1,first.2.2.2,
    canonical_assertions base initial w.registry.value w.registry.audit.epoch w.registry.position
      legal.2.2.2.2.2.2.1 zero⟩
end ShielddSecurity.CapturedValueGlobal108

set_option pp.all true in
#check @ShielddSecurity.CapturedValueGlobal108.completed
#print axioms ShielddSecurity.CapturedValueGlobal108.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedValueGlobal108.bits
#print axioms ShielddSecurity.CapturedValueGlobal108.bits
set_option pp.all true in
#check @ShielddSecurity.CapturedValueGlobal108.zero
#print axioms ShielddSecurity.CapturedValueGlobal108.zero
set_option pp.all true in
#check @ShielddSecurity.CapturedValueGlobal108.canonical_assertions
#print axioms ShielddSecurity.CapturedValueGlobal108.canonical_assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedValueGlobal108.legal_registry_global422
#print axioms ShielddSecurity.CapturedValueGlobal108.legal_registry_global422
