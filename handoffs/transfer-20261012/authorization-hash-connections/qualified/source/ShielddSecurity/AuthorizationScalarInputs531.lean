import ShielddSecurity.AuthorizationAkFrame516
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationScalarInputs531
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint
structure Inputs (rho : Nat → F) (w : TransferSem.Witness) : Prop where
  key : rho 1993=(w.auth.nk:F)
  quotient : rho 1994=(w.auth.quotient:F)
  ivk : rho 1995=(w.auth.ivk:F)
theorem base (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial)
      c w initial senderInitial receiverInitial) w := by
  refine ⟨AuthorizationPointFrame407.completed_key original c w authInitial initial senderInitial receiverInitial,?_,?_⟩
  · simpa only [AuthScalarSeed366.value,if_pos rfl] using
      SemanticWordFrame373.auth_value (AuthorizationPointSeed405.seed original w authInitial)
        c w initial senderInitial receiverInitial 1994 (by decide)
  · simpa only [AuthScalarSeed366.value,if_neg (show (1995:Nat)≠1994 by decide),if_pos rfl] using
      SemanticWordFrame373.auth_value (AuthorizationPointSeed405.seed original w authInitial)
        c w initial senderInitial receiverInitial 1995 (by decide)
theorem shared (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial) w :=
  base (AuthorizationSharedSeed416.seed original c w) c w authInitial initial senderInitial receiverInitial
theorem trace (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationTraceAssignment457.assignment original c w legal authInitial initial senderInitial receiverInitial) w :=
  shared (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (AuthorizationTraceAssignment457.bases c w legal) w.auth.ivk) w)
    (ConcreteAuthorizationCrypto430.withOperations c) w authInitial initial senderInitial receiverInitial
theorem dh (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationDhSeed473.assignment original c w legal authInitial initial senderInitial receiverInitial) w :=
  trace (AuthorizationDhSeed473.seed original c w legal) c w legal authInitial initial senderInitial receiverInitial
theorem fixed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationFixedSeed487.assignment original c w legal authInitial initial senderInitial receiverInitial) w :=
  dh (AuthorizationFixedSeed487.seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial
theorem rk (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w :=
  fixed (AuthorizationRkSeed505.seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial
end ShielddSecurity.AuthorizationScalarInputs531
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.Inputs
#print axioms ShielddSecurity.AuthorizationScalarInputs531.Inputs
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.base
#print axioms ShielddSecurity.AuthorizationScalarInputs531.base
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.shared
#print axioms ShielddSecurity.AuthorizationScalarInputs531.shared
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.trace
#print axioms ShielddSecurity.AuthorizationScalarInputs531.trace
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.dh
#print axioms ShielddSecurity.AuthorizationScalarInputs531.dh
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.fixed
#print axioms ShielddSecurity.AuthorizationScalarInputs531.fixed
set_option pp.all true in
#check @ShielddSecurity.AuthorizationScalarInputs531.rk
#print axioms ShielddSecurity.AuthorizationScalarInputs531.rk
