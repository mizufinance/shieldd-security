import ShielddSecurity.AuthorizationPointFrame407
import ShielddSecurity.AuthorizationClampConstruction403
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPointConstruction408
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F, ∃ receiverInitial : Fin 3 → Group.Point F,
    ∃ initial : Fin 4 → Group.Point F,
      Group.OnCurve (CapturedFirstSubgroup81.d:F) authInitial ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) authInitial=SubgroupSeedCompletion203.fieldPoint w.auth.ak ∧
      (((((((LegalSharedRows271.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      ComparisonConstruction328.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      HighZeroConstruction334.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 ∧
      SharedCanonicalRows340.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      SharedUserLifecycle348.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      UserSubgroupCapture355.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      CapturedUserNonidentity358.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial) ∧
      (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial 1528=(w.sender.rnkCommitment:F) ∧
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial 1766=(w.receiver.rnkCommitment:F)) ∧
      (∀ (level : Fin 16) (slot : Fin 3),
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial (1531+3*level.val+slot.val)=(w.sender.siblings level slot:F) ∧
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial (1769+3*level.val+slot.val)=(w.receiver.siblings level slot:F)) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed (AuthorizationPointSeed405.seed original w authInitial) w) w) w) w senderInitial receiverInitial) c w initial 2) = w.blinding) ∧
      (∀ column∈AuthScalarSeed366.values,
       SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial column=(AuthScalarSeed366.value w column:F)) ∧
      (∀ column∈RemainingWordSeed369.values,
       SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial column=(RemainingWordSeed369.value w column:F))) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (185562+index)) 2) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (179950+index)) 2) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (180205+index)) 2) ∧
      SharedScalarCanonical396.Rows
        (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial)) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (180208+index)) 2) ∧
      (∀ offset : Fin 8,
        SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial
          (1980+offset.val)=AuthorizationPointSeed405.value w authInitial offset.val) ∧
      SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial 1993=(w.auth.nk:F) := by
  obtain ⟨authInitial,onCurve,eight⟩ := AuthorizationPointDomain404.preimage c w legal
  obtain ⟨senderInitial,receiverInitial,initial,previous⟩ := AuthorizationClampConstruction403.legal_completed
    (AuthorizationPointSeed405.seed original w authInitial) c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,onCurve,eight,previous,
    fun offset => AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial offset,
    AuthorizationPointFrame407.completed_key original c w authInitial initial senderInitial receiverInitial⟩

end ShielddSecurity.AuthorizationPointConstruction408
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointConstruction408.legal_completed
#print axioms ShielddSecurity.AuthorizationPointConstruction408.legal_completed
