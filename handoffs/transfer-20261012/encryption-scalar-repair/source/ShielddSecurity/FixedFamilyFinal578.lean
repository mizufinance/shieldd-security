import ShielddSecurity.PayloadBindings565
import ShielddSecurity.AuthorizationFixedLocal493
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyFinal578
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open FixedFamilyLayout545
open PayloadBindings565 (assignment)
attribute [local irreducible] assignment model

theorem semantic_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (pointStart family+250)=
      SubgroupSeedCompletion203.fieldPoint ((AuthorizationFixedDomain485.crypto c).mul
        (scalar w family) (AuthorizationFixedDomain485.crypto c).generator) := by
  unfold assignment
  have bound := SharedScalarCanonical396.all_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c))
    w legal (scalarFamily family)
  have point := FixedFamilyBindings551.point (PayloadTraceSeed564.seed original c w legal)
    c w legal rkInitial authInitial initial senderInitial receiverInitial family 125 (by decide)
  exact (point.trans (AuthorizationFixedLocal493.last_output (scalar w family) (lt_trans bound (by decide)))).trans
    (AuthorizationFixedDomain485.multiply_coordinates c (scalar w family)
      (lt_trans bound (by decide))).symm

end ShielddSecurity.FixedFamilyFinal578
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyFinal578.semantic_point
#print axioms ShielddSecurity.FixedFamilyFinal578.semantic_point
