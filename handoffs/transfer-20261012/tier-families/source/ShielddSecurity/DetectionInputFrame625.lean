import ShielddSecurity.AuthorizationScalarInputs531
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionInputFrame625
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SubgroupSeedCompletion203.fieldPoint
structure Inputs (rho : Nat → F) (w : TransferSem.Witness) : Prop where
  asset : rho 6=(w.asset:F)
  flag : rho 10=(if w.regulated then 1 else 0)
  detectionX : rho 14=(w.registry.detection.x:F)
  detectionY : rho 15=(w.registry.detection.y:F)
  commitment : rho 1528=(w.sender.rnkCommitment:F)
set_option pp.all true in
#check @Inputs
#print axioms Inputs
attribute [local irreducible] UserLifecycleWord345.assignment UserSubgroupSeed352.seed UserPathSeed361.seed AuthScalarSeed366.seed RemainingWordSeed369.seed
theorem base_commitment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial 1528=(w.sender.rnkCommitment:F) :=
  (UserPathFrame363.commitments (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w)
    c w initial senderInitial receiverInitial).1
attribute [local semireducible] UserLifecycleWord345.assignment UserSubgroupSeed352.seed UserPathSeed361.seed AuthScalarSeed366.seed RemainingWordSeed369.seed
attribute [local irreducible] SemanticWordFrame373.assignment

set_option pp.all true in
#check @base_commitment
#print axioms base_commitment
attribute [local semireducible] SemanticWordFrame373.assignment
theorem header (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    let rho := AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial
    rho 6=(w.asset:F) ∧ rho 10=(if w.regulated then 1 else 0) ∧
      rho 14=(w.registry.detection.x:F) ∧ rho 15=(w.registry.detection.y:F) := by
  let base := AuthorizationSharedFrame420B.originalBase original c w authInitial senderInitial receiverInitial
  let rho := AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial
  have asset : rho 6=(w.asset:F) := SharedRegulatedValue316.asset_meaning base c w initial
  have flag : rho 10=(if w.regulated then 1 else 0) := SharedRegulatedValue316.control_meaning base c w initial
  have detectionX : rho 14=(w.registry.detection.x:F) :=
    (SharedRegulatedValue316.original_frame base c w initial 14 (by constructor <;> decide) (by decide)).trans
      ((RegisteredConstructorFrame309.prepared_outside base c w 14 (by decide) (by constructor <;> decide)).trans
        (RegistryNaturalSeed298.seed_fixed _ _ 14 (by decide)))
  have detectionY : rho 15=(w.registry.detection.y:F) :=
    (SharedRegulatedValue316.original_frame base c w initial 15 (by constructor <;> decide) (by decide)).trans
      ((RegisteredConstructorFrame309.prepared_outside base c w 15 (by decide) (by constructor <;> decide)).trans
        (RegistryNaturalSeed298.seed_fixed _ _ 15 (by decide)))
  exact ⟨asset,flag,detectionX,detectionY⟩
set_option pp.all true in
#check @header
#print axioms header
attribute [local irreducible] SemanticWordFrame373.assignment
theorem shared (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial) w := by
  have h := header original c w authInitial initial senderInitial receiverInitial
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,base_commitment
    (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial)
    c w initial senderInitial receiverInitial⟩
set_option pp.all true in
#check @shared
#print axioms shared
theorem trace (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationTraceAssignment457.assignment original c w legal authInitial initial senderInitial receiverInitial) w :=
  shared (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (AuthorizationTraceAssignment457.bases c w legal) w.auth.ivk) w)
    (ConcreteAuthorizationCrypto430.withOperations c) w authInitial initial senderInitial receiverInitial
set_option pp.all true in
#check @trace
#print axioms trace
theorem dh (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationDhSeed473.assignment original c w legal authInitial initial senderInitial receiverInitial) w :=
  trace (AuthorizationDhSeed473.seed original c w legal) c w legal authInitial initial senderInitial receiverInitial
set_option pp.all true in
#check @dh
#print axioms dh
theorem fixed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationFixedSeed487.assignment original c w legal authInitial initial senderInitial receiverInitial) w :=
  dh (AuthorizationFixedSeed487.seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial
set_option pp.all true in
#check @fixed
#print axioms fixed
theorem rk (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Inputs (AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w :=
  fixed (AuthorizationRkSeed505.seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial
set_option pp.all true in
#check @rk
#print axioms rk
end ShielddSecurity.DetectionInputFrame625
