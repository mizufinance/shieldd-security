import ShielddSecurity.AuthorizationDhDomain471
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationDhColumn476
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457
attribute [local irreducible] assignment model
theorem completed_x (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial 3763=(AuthorizationDhDomain471.point c w legal).x :=
  by
  have final := AuthorizationFinalPoint467.final_point original c w legal authInitial initial senderInitial receiverInitial 1 (by decide)
  simpa only [AuthorizationDhDomain471.point, VariableWindowColumns449.columnPoint, Nat.mul_one, Nat.reduceAdd] using
    congrArg (fun value : Group.Point F => value.x) final

end ShielddSecurity.AuthorizationDhColumn476
set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhColumn476.completed_x
#print axioms ShielddSecurity.AuthorizationDhColumn476.completed_x
