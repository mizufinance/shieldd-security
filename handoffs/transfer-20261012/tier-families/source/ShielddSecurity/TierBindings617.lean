import ShielddSecurity.TierTrace616
import ShielddSecurity.RkScalarFrame550
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierBindings617
open ConcreteJubjubField01 TransferSem TierLayout613
open AuthorizationTraceSeed451 (hintPoint)
attribute [local irreducible] SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  OwnershipBindings604.assignment (TierTrace616.seed original c w legal) (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem start_member (family : Fin 5) : pointStart family∈starts := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl <;> decide

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) (index : Nat) (before : index<378) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (pointStart family+2*index)=hintPoint (TierGroupDomain612.represented c w family legal) (scalar w family) index := by
  unfold assignment
  have x := TierFrame615.ownership_frame (TierTrace616.seed original c w legal) (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  have y := TierFrame615.ownership_frame (TierTrace616.seed original c w legal) (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index+1)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  exact (congrArg₂ Group.Point.mk x y).trans (TierTrace616.point original c w legal family index before)

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) (index : Nat) (bound : index<252) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
      (ScalarCanonicalRows395.bitStart (scalarFamily family)+index)=
      if (encodeBits 252 (scalar w family))[index]?.getD false then 1 else 0 := by
  unfold assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact RkScalarFrame550.bits _ (DetectionGroupDomain611.baseCrypto c) w legal rkInitial authInitial initial senderInitial receiverInitial
    (scalarFamily family) index bound

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact OwnershipBindings604.arithmetic (TierTrace616.seed original c w legal) (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial CompilerArithmeticTransport41.copy=1 := by
  unfold assignment
  exact OwnershipBindings604.copied (TierTrace616.seed original c w legal) (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.TierBindings617

set_option pp.all true in
#check @ShielddSecurity.TierBindings617.assignment
#print axioms ShielddSecurity.TierBindings617.assignment

set_option pp.all true in
#check @ShielddSecurity.TierBindings617.start_member
#print axioms ShielddSecurity.TierBindings617.start_member

set_option pp.all true in
#check @ShielddSecurity.TierBindings617.point
#print axioms ShielddSecurity.TierBindings617.point

set_option pp.all true in
#check @ShielddSecurity.TierBindings617.bits
#print axioms ShielddSecurity.TierBindings617.bits

set_option pp.all true in
#check @ShielddSecurity.TierBindings617.arithmetic
#print axioms ShielddSecurity.TierBindings617.arithmetic

set_option pp.all true in
#check @ShielddSecurity.TierBindings617.copied
#print axioms ShielddSecurity.TierBindings617.copied
