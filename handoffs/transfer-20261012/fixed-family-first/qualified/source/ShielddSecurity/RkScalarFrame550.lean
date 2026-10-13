import ShielddSecurity.AuthorizationRkSeed505
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RkScalarFrame550
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] SemanticWordFrame373.assignment model

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 9) (index : Nat) (bound : index<252) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
      (ScalarCanonicalRows395.bitStart family+index)=
      if (encodeBits 252 (SharedScalarCanonical396.numbers w family))[index]?.getD false then 1 else 0 := by
  let chosen := AuthorizationFixedDomain485.withGenerator c
  let fixed := AuthorizationFixedSeed487.seed (AuthorizationRkSeed505.seed original w rkInitial) w.auth.randomizer
  let inner := IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed
    (AuthorizationDhSeed473.seed fixed chosen w legal)
    (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk) w
  exact SharedScalarCanonical396.all_bits
    (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed inner (ConcreteAuthorizationCrypto430.withOperations chosen) w) w authInitial)
    (ConcreteAuthorizationCrypto430.withOperations chosen) w initial senderInitial receiverInitial legal family index bound
end ShielddSecurity.RkScalarFrame550
set_option pp.all true in
#check @ShielddSecurity.RkScalarFrame550.bits
#print axioms ShielddSecurity.RkScalarFrame550.bits
