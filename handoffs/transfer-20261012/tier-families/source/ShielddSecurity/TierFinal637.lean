import ShielddSecurity.TierFlagBindings630
import ShielddSecurity.AuthorizationFinalPoint467
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFinal637
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierLayout613 AuthorizationTraceSeed451
open TierFlagBindings630 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model

theorem final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (pointStart family+754)=
      SubgroupSeedCompletion203.fieldPoint ((DetectionGroupDomain611.crypto c).mul
        (scalar w family) (TierGroupDomain612.selected c w family)) := by
  have bound := SharedScalarCanonical396.all_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator (DetectionGroupDomain611.baseCrypto c))) w legal (scalarFamily family)
  have small : scalar w family<2^252 := lt_trans bound (by decide)
  have point := TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 377 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family+754)=
    (windowAt (TierGroupDomain612.represented c w family legal) (scalar w family) 125).output at point
  rw [AuthorizationFinalPoint467.last_output _ _ small] at point
  have multiplication := TierGroupDomain612.multiplication c w family legal (scalar w family)
    (lt_trans small (by decide))
  exact point.trans multiplication.symm
end ShielddSecurity.TierFinal637
set_option pp.all true in
#check @ShielddSecurity.TierFinal637.final_point
#print axioms ShielddSecurity.TierFinal637.final_point
