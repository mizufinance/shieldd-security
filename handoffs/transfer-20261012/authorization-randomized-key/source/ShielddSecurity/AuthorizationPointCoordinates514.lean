import ShielddSecurity.AuthorizationPointFrame407
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPointCoordinates514
open ConcreteJubjubField01 TransferSem

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Group.Point.mk
      (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial 1980)
      (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial 1981)=
    SubgroupSeedCompletion203.fieldPoint w.auth.ak := by
  have x := AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨0,by decide⟩
  have y := AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨1,by decide⟩
  exact congrArg₂ Group.Point.mk x y
end ShielddSecurity.AuthorizationPointCoordinates514
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointCoordinates514.point
#print axioms ShielddSecurity.AuthorizationPointCoordinates514.point
