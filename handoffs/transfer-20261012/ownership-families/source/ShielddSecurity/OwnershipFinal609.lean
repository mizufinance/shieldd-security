import ShielddSecurity.OwnershipBindings604
import ShielddSecurity.AuthorizationFinalPoint467
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipFinal609
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open OwnershipLayout600 AuthorizationTraceSeed451
open OwnershipBindings604 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model

theorem scalar_output (w : TransferSem.Witness) (family : Fin 2) :
    scalar w family=(w.encryption.ownership family).randomness := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl <;> rfl

theorem final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (pointStart family+754)=
      SubgroupSeedCompletion203.fieldPoint ((AuthorizationFixedDomain485.crypto c).mul
        (w.encryption.ownership family).randomness (checkingKey (AuthorizationFixedDomain485.crypto c) w)) := by
  have bound := SharedScalarCanonical396.all_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal (scalarFamily family)
  have small : scalar w family<2^252 := lt_trans bound (by decide)
  have point := OwnershipBindings604.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 377 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family+754)=
    (windowAt (CheckingGroupDomain595.represented c w legal) (scalar w family) 125).output at point
  rw [AuthorizationFinalPoint467.last_output _ _ small] at point
  have multiplication := CheckingGroupDomain595.multiplication c w legal (scalar w family)
    (lt_trans small (by decide))
  rw [scalar_output w family] at multiplication point
  exact point.trans multiplication.symm
end ShielddSecurity.OwnershipFinal609
set_option pp.all true in
#check @ShielddSecurity.OwnershipFinal609.scalar_output
#print axioms ShielddSecurity.OwnershipFinal609.scalar_output
set_option pp.all true in
#check @ShielddSecurity.OwnershipFinal609.final_point
#print axioms ShielddSecurity.OwnershipFinal609.final_point
