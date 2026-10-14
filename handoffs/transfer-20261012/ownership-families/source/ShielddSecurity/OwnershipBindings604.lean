import ShielddSecurity.CheckingBase598
import ShielddSecurity.OwnershipTrace603
import ShielddSecurity.RkScalarFrame550
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipBindings604
open ConcreteJubjubField01 TransferSem OwnershipLayout600
open AuthorizationTraceSeed451 (hintPoint)
attribute [local irreducible] SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  PublishedInverseSeed592.assignment (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem start_member (family : Fin 2) : pointStart family∈starts := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl <;> decide

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) (index : Nat) (before : index<378) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (pointStart family+2*index)=hintPoint (CheckingGroupDomain595.represented c w legal) (scalar w family) index := by
  unfold assignment
  have x := OwnershipFrame602.retained_frame_full (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  have y := OwnershipFrame602.retained_frame_full (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index+1)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  exact (congrArg₂ Group.Point.mk x y).trans (OwnershipTrace603.point original c w legal family index before)

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) (index : Nat) (bound : index<252) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
      (ScalarCanonicalRows395.bitStart (scalarFamily family)+index)=
      if (encodeBits 252 (scalar w family))[index]?.getD false then 1 else 0 := by
  unfold assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact RkScalarFrame550.bits _ c w legal rkInitial authInitial initial senderInitial receiverInitial
    (scalarFamily family) index bound

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact PublishedInverseSeed592.arithmetic (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial CompilerArithmeticTransport41.copy=1 := by
  unfold assignment
  exact PublishedInverseSeed592.copied (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
theorem base (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowJoin443.point
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      CheckingBase598.baseX CheckingBase598.baseY=
      ConcreteRegistrySharedEncoding294.model.coordinates (CheckingGroupDomain595.represented c w legal) := by
  unfold assignment
  exact CheckingBase598.coordinates (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial

end ShielddSecurity.OwnershipBindings604
set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.assignment
#print axioms ShielddSecurity.OwnershipBindings604.assignment
set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.start_member
#print axioms ShielddSecurity.OwnershipBindings604.start_member
set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.point
#print axioms ShielddSecurity.OwnershipBindings604.point
set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.bits
#print axioms ShielddSecurity.OwnershipBindings604.bits
set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.arithmetic
#print axioms ShielddSecurity.OwnershipBindings604.arithmetic
set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.copied
#print axioms ShielddSecurity.OwnershipBindings604.copied

set_option pp.all true in
#check @ShielddSecurity.OwnershipBindings604.base
#print axioms ShielddSecurity.OwnershipBindings604.base
