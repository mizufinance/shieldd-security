import ShielddSecurity.AuthorizationRkSeed505
import ShielddSecurity.AuthorizationPointCoordinates514
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRandomizerBindings515
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationRkSeed505 (assignment seed)
attribute [local irreducible] SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint assignment model

theorem right (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) 4269=
      AuthorizationAddDomain504.right w := by
  unfold assignment AuthorizationAddDomain504.right
  exact AuthorizationFixedFinal500.final_point (seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial
end ShielddSecurity.AuthorizationRandomizerBindings515
set_option pp.all true in
#check @ShielddSecurity.AuthorizationRandomizerBindings515.right
#print axioms ShielddSecurity.AuthorizationRandomizerBindings515.right
