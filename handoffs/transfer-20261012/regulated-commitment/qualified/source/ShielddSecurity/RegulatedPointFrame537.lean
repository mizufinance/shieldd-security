import ShielddSecurity.AuthorizationScalarInputs531
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegulatedPointFrame537
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open VariableWindowColumns449
attribute [local irreducible] SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint
  AuthorizationTraceAssignment457.assignment model
structure Points (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness) : Prop where
  sender : ∀ slot : Fin 3, columnPoint rho (1504+8*slot.val)=
    SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.sender slot)
  dh : columnPoint rho 3763=SubgroupSeedCompletion203.fieldPoint ((ConcreteAuthorizationCrypto430.crypto c).mul w.auth.ivk w.sender.rnkDH)
theorem trace (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Points (AuthorizationTraceAssignment457.assignment original c w legal authInitial initial senderInitial receiverInitial) c w := by
  refine ⟨AuthorizationTraceBindings458.sender_point original c w legal authInitial initial senderInitial receiverInitial,?_⟩
  have final := AuthorizationFinalPoint467.final_point original c w legal authInitial initial senderInitial receiverInitial 1 (by decide)
  have coordinates : columnPoint (AuthorizationTraceAssignment457.assignment original c w legal authInitial initial senderInitial receiverInitial) 3763=
      AuthorizationDhDomain471.point c w legal := by
    simpa only [AuthorizationDhDomain471.point,Nat.mul_one,Nat.reduceAdd] using final
  exact coordinates.trans (AuthorizationDhDomain471.coordinates c w legal).symm
theorem dh (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Points (AuthorizationDhSeed473.assignment original c w legal authInitial initial senderInitial receiverInitial) c w := by
  unfold AuthorizationDhSeed473.assignment
  exact trace (AuthorizationDhSeed473.seed original c w legal) c w legal authInitial initial senderInitial receiverInitial
theorem fixed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Points (AuthorizationFixedSeed487.assignment original c w legal authInitial initial senderInitial receiverInitial)
      (AuthorizationFixedDomain485.withGenerator c) w :=
  dh (AuthorizationFixedSeed487.seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial
theorem rk (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Points (AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (AuthorizationFixedDomain485.withGenerator c) w :=
  fixed (AuthorizationRkSeed505.seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial
end ShielddSecurity.RegulatedPointFrame537
set_option pp.all true in
#check @ShielddSecurity.RegulatedPointFrame537.Points
#print axioms ShielddSecurity.RegulatedPointFrame537.Points
set_option pp.all true in
#check @ShielddSecurity.RegulatedPointFrame537.trace
#print axioms ShielddSecurity.RegulatedPointFrame537.trace
set_option pp.all true in
#check @ShielddSecurity.RegulatedPointFrame537.dh
#print axioms ShielddSecurity.RegulatedPointFrame537.dh
set_option pp.all true in
#check @ShielddSecurity.RegulatedPointFrame537.fixed
#print axioms ShielddSecurity.RegulatedPointFrame537.fixed
set_option pp.all true in
#check @ShielddSecurity.RegulatedPointFrame537.rk
#print axioms ShielddSecurity.RegulatedPointFrame537.rk
