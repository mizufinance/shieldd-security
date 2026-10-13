import ShielddSecurity.AuthorizationPointCoordinates514
import ShielddSecurity.AuthorizationRkSeed505
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationAkFrame516
open ConcreteJubjubField01 TransferSem
open VariableWindowColumns449
attribute [local irreducible] SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint

theorem shared (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    columnPoint (AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial) 1980=
      SubgroupSeedCompletion203.fieldPoint w.auth.ak := by
  simpa only [columnPoint,AuthorizationSharedFrame420B.assignment,SharedAuthorizationNonidentity413.assignment]
    using AuthorizationPointCoordinates514.point (AuthorizationSharedSeed416.seed original c w)
      c w authInitial initial senderInitial receiverInitial

theorem trace (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    columnPoint (AuthorizationTraceAssignment457.assignment original c w legal authInitial initial senderInitial receiverInitial) 1980=
      SubgroupSeedCompletion203.fieldPoint w.auth.ak :=
  shared (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (AuthorizationTraceAssignment457.bases c w legal) w.auth.ivk) w)
    (ConcreteAuthorizationCrypto430.withOperations c) w authInitial initial senderInitial receiverInitial

theorem dh (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    columnPoint (AuthorizationDhSeed473.assignment original c w legal authInitial initial senderInitial receiverInitial) 1980=
      SubgroupSeedCompletion203.fieldPoint w.auth.ak :=
  trace (AuthorizationDhSeed473.seed original c w legal) c w legal authInitial initial senderInitial receiverInitial

theorem fixed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    columnPoint (AuthorizationFixedSeed487.assignment original c w legal authInitial initial senderInitial receiverInitial) 1980=
      SubgroupSeedCompletion203.fieldPoint w.auth.ak :=
  dh (AuthorizationFixedSeed487.seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial
end ShielddSecurity.AuthorizationAkFrame516

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAkFrame516.shared
#print axioms ShielddSecurity.AuthorizationAkFrame516.shared

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAkFrame516.trace
#print axioms ShielddSecurity.AuthorizationAkFrame516.trace

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAkFrame516.dh
#print axioms ShielddSecurity.AuthorizationAkFrame516.dh

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAkFrame516.fixed
#print axioms ShielddSecurity.AuthorizationAkFrame516.fixed
