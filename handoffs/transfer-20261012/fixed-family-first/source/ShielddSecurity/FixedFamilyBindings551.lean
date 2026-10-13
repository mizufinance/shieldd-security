import ShielddSecurity.FixedFamilySeed549
import ShielddSecurity.RkScalarFrame550
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyBindings551
open ConcreteJubjubField01 TransferSem FixedFamilyLayout545
open AuthorizationFixedSeed487 (window)
attribute [local irreducible] SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  AuthorizationRkSeed505.assignment (FixedFamilySeed549.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem start_member (family : Fin 8) : pointStart family∈starts := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨
      family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨ family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) (index : Nat) (before : index<126) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (pointStart family+2*index)=(window (scalar w family) index).output := by
  unfold assignment
  have x := FixedFamilyFrame547.rk_frame (FixedFamilySeed549.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  have y := FixedFamilyFrame547.rk_frame (FixedFamilySeed549.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index+1)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  exact (congrArg₂ Group.Point.mk x y).trans (FixedFamilySeed549.point original w family index before)

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) (index : Nat) (bound : index<252) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
      (ScalarCanonicalRows395.bitStart (scalarFamily family)+index)=
      if (encodeBits 252 (scalar w family))[index]?.getD false then 1 else 0 := by
  unfold assignment
  exact RkScalarFrame550.bits (FixedFamilySeed549.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (scalarFamily family) index bound

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact AuthorizationRkSeed505.arithmetic (FixedFamilySeed549.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial CompilerArithmeticTransport41.copy=1 := by
  unfold assignment
  exact AuthorizationRkSeed505.copied (FixedFamilySeed549.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.FixedFamilyBindings551
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyBindings551.assignment
#print axioms ShielddSecurity.FixedFamilyBindings551.assignment
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyBindings551.start_member
#print axioms ShielddSecurity.FixedFamilyBindings551.start_member
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyBindings551.point
#print axioms ShielddSecurity.FixedFamilyBindings551.point
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyBindings551.bits
#print axioms ShielddSecurity.FixedFamilyBindings551.bits
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyBindings551.arithmetic
#print axioms ShielddSecurity.FixedFamilyBindings551.arithmetic
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyBindings551.copied
#print axioms ShielddSecurity.FixedFamilyBindings551.copied
