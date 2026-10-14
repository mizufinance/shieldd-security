import ShielddSecurity.PayloadBindings565
import ShielddSecurity.AuthorizationFinalPoint467
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadFinal575
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open PayloadFamilyLayout559 AuthorizationTraceSeed451
open PayloadBindings565 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model

theorem scalar_output (w : TransferSem.Witness) (family : Fin 2) :
    scalar w family=(w.outputs family).recovery.randomizer := by
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
        (w.outputs family).recovery.randomizer (payloadKey (AuthorizationFixedDomain485.crypto c) w)) := by
  have bound := SharedScalarCanonical396.all_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal (scalarFamily family)
  have small : scalar w family<2^252 := lt_trans bound (by decide)
  have point := PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 377 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family+754)=
    (windowAt (PayloadGroupDomain557.represented c w legal) (scalar w family) 125).output at point
  rw [AuthorizationFinalPoint467.last_output _ _ small] at point
  have multiplication := PayloadGroupDomain557.multiplication c w legal (scalar w family)
    (lt_trans small (by decide))
  rw [scalar_output w family] at multiplication point
  exact point.trans multiplication.symm
end ShielddSecurity.PayloadFinal575
set_option pp.all true in
#check @ShielddSecurity.PayloadFinal575.scalar_output
#print axioms ShielddSecurity.PayloadFinal575.scalar_output
set_option pp.all true in
#check @ShielddSecurity.PayloadFinal575.final_point
#print axioms ShielddSecurity.PayloadFinal575.final_point
