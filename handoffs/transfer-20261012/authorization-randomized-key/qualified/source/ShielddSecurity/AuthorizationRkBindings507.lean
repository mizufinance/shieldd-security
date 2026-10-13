import ShielddSecurity.AuthorizationRkSeed505
import ShielddSecurity.AuthorizationRkCapture506B05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkBindings507
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationRkSeed505 (assignment seed value)
attribute [local irreducible] assignment

theorem input_roles (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (binding : CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) rkInitial=SubgroupSeedCompletion203.fieldPoint w.auth.rk) :
    CapturedFourSubgroupConstructor88.InputRoles
      (fun column => assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
        (AuthorizationRkCapture506B05.rename column)) rkInitial := by
  have stored := AuthorizationRkSeed505.completed_value original c w legal rkInitial authInitial initial senderInitial receiverInitial
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (stored ⟨0,by decide⟩).trans (congrArg Group.Point.x binding).symm
  · exact (stored ⟨1,by decide⟩).trans (congrArg Group.Point.y binding).symm
  · exact stored ⟨2,by decide⟩
  · exact stored ⟨3,by decide⟩
  · intro index before
    have cases : index=0 ∨ index=1 ∨ index=2 := by omega
    rcases cases with rfl|rfl|rfl
    · exact stored ⟨4,by decide⟩
    · exact stored ⟨5,by decide⟩
    · exact stored ⟨6,by decide⟩

theorem subgroup_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (valid : Group.OnCurve (CapturedFirstSubgroup81.d:F) rkInitial)
    (binding : CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) rkInitial=SubgroupSeedCompletion203.fieldPoint w.auth.rk) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+4281+i)) 6 := by
  have zero := AuthorizationRkSeed505.zero original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := AuthorizationRkSeed505.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  exact AuthorizationRkCapture506B05.complete _ rkInitial imaginary zero (copied.trans zero.symm)
    (AuthorizationRkSeed505.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (input_roles original c w legal rkInitial authInitial initial senderInitial receiverInitial binding)
    valid (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) 4272=
      SubgroupSeedCompletion203.fieldPoint w.auth.rk := by
  exact congrArg₂ Group.Point.mk
    (AuthorizationRkSeed505.completed_value original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩)
    (AuthorizationRkSeed505.completed_value original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩)

theorem inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 4279=(w.auth.rk.x:F)⁻¹ :=
  AuthorizationRkSeed505.completed_value original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨7,by decide⟩
end ShielddSecurity.AuthorizationRkBindings507

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkBindings507.input_roles
#print axioms ShielddSecurity.AuthorizationRkBindings507.input_roles

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkBindings507.subgroup_rows
#print axioms ShielddSecurity.AuthorizationRkBindings507.subgroup_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkBindings507.point
#print axioms ShielddSecurity.AuthorizationRkBindings507.point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkBindings507.inverse
#print axioms ShielddSecurity.AuthorizationRkBindings507.inverse
