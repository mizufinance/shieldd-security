import ShielddSecurity.PayloadTraceSeed564
import ShielddSecurity.RkScalarFrame550
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadBindings565
open ConcreteJubjubField01 TransferSem PayloadFamilyLayout559
open AuthorizationTraceSeed451 (hintPoint)
attribute [local irreducible] SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  FixedFamilyBindings551.assignment (PayloadTraceSeed564.seed original c w legal) c w legal
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
      (pointStart family+2*index)=hintPoint (PayloadGroupDomain557.represented c w legal) (scalar w family) index := by
  unfold assignment
  have x := PayloadFamilyFrame561.retained_frame (PayloadTraceSeed564.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  have y := PayloadFamilyFrame561.retained_frame (PayloadTraceSeed564.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (pointStart family+2*index+1)
    ⟨pointStart family,start_member family,by omega,by omega⟩
  exact (congrArg₂ Group.Point.mk x y).trans (PayloadTraceSeed564.point original c w legal family index before)

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) (index : Nat) (bound : index<252) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
      (ScalarCanonicalRows395.bitStart (scalarFamily family)+index)=
      if (encodeBits 252 (scalar w family))[index]?.getD false then 1 else 0 := by
  unfold assignment
  unfold FixedFamilyBindings551.assignment
  exact RkScalarFrame550.bits (FixedFamilySeed549.seed (PayloadTraceSeed564.seed original c w legal) w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial (scalarFamily family) index bound

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact FixedFamilyBindings551.arithmetic (PayloadTraceSeed564.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial CompilerArithmeticTransport41.copy=1 := by
  unfold assignment
  exact FixedFamilyBindings551.copied (PayloadTraceSeed564.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.PayloadBindings565
set_option pp.all true in
#check @ShielddSecurity.PayloadBindings565.assignment
#print axioms ShielddSecurity.PayloadBindings565.assignment
set_option pp.all true in
#check @ShielddSecurity.PayloadBindings565.start_member
#print axioms ShielddSecurity.PayloadBindings565.start_member
set_option pp.all true in
#check @ShielddSecurity.PayloadBindings565.point
#print axioms ShielddSecurity.PayloadBindings565.point
set_option pp.all true in
#check @ShielddSecurity.PayloadBindings565.bits
#print axioms ShielddSecurity.PayloadBindings565.bits
set_option pp.all true in
#check @ShielddSecurity.PayloadBindings565.arithmetic
#print axioms ShielddSecurity.PayloadBindings565.arithmetic
set_option pp.all true in
#check @ShielddSecurity.PayloadBindings565.copied
#print axioms ShielddSecurity.PayloadBindings565.copied
