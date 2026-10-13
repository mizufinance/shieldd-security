import ShielddSecurity.AuthorizationFixedInitial499
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedFinal500
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationFixedSeed487 (assignment window)
attribute [local irreducible] assignment

theorem final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal authInitial initial senderInitial receiverInitial) 4269=
      model.coordinates (w.auth.randomizer • AuthorizationFixedDomain485.represented) := by
  have point := AuthorizationFixedBindings492.point original c w legal authInitial initial senderInitial receiverInitial 125 (by decide)
  have bound := (AuthScalarSeed366.legal_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal).2.2
  exact point.trans (AuthorizationFixedLocal493.last_output w.auth.randomizer bound)

theorem semantic_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal authInitial initial senderInitial receiverInitial) 4269=
      SubgroupSeedCompletion203.fieldPoint ((AuthorizationFixedDomain485.crypto c).mul
        w.auth.randomizer (AuthorizationFixedDomain485.crypto c).generator) := by
  have bound := (AuthScalarSeed366.legal_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal).2.2
  have wider : w.auth.randomizer<2^255 := lt_trans bound (by decide)
  exact (final_point original c w legal authInitial initial senderInitial receiverInitial).trans
    (AuthorizationFixedDomain485.multiply_coordinates c w.auth.randomizer wider).symm
end ShielddSecurity.AuthorizationFixedFinal500
set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedFinal500.final_point
#print axioms ShielddSecurity.AuthorizationFixedFinal500.final_point
set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedFinal500.semantic_point
#print axioms ShielddSecurity.AuthorizationFixedFinal500.semantic_point
