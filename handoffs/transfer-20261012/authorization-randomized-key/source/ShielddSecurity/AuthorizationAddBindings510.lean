import ShielddSecurity.AuthorizationRkSeed505
import ShielddSecurity.AuthorizationAkFrame516
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationAddBindings510
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationRkSeed505 (assignment seed)
attribute [local irreducible] assignment model SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint

theorem left (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) 1980=
      AuthorizationAddDomain504.left w := by
  unfold assignment AuthorizationAddDomain504.left
  exact AuthorizationAkFrame516.fixed (seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial

end ShielddSecurity.AuthorizationAddBindings510
set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddBindings510.left
#print axioms ShielddSecurity.AuthorizationAddBindings510.left
