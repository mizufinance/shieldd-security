import ShielddSecurity.SharedScalarCanonical396
import ShielddSecurity.IvkCanonicalConstruction391
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ScalarCanonicalConstruction397
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∃ senderInitial : Fin 3 → Group.Point F, ∃ receiverInitial : Fin 3 → Group.Point F,
    ∃ initial : Fin 4 → Group.Point F,
      (((((LegalSharedRows271.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      ComparisonConstruction328.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      HighZeroConstruction334.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 ∧
      SharedCanonicalRows340.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      SharedUserLifecycle348.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      UserSubgroupCapture355.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      CapturedUserNonidentity358.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial) ∧
      (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial 1528=(w.sender.rnkCommitment:F) ∧
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial 1766=(w.receiver.rnkCommitment:F)) ∧
      (∀ (level : Fin 16) (slot : Fin 3),
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial (1531+3*level.val+slot.val)=(w.sender.siblings level slot:F) ∧
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial (1769+3*level.val+slot.val)=(w.receiver.siblings level slot:F)) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w senderInitial receiverInitial) c w initial 2) = w.blinding) ∧
      (∀ column∈AuthScalarSeed366.values,
       SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial column=(AuthScalarSeed366.value w column:F)) ∧
      (∀ column∈RemainingWordSeed369.values,
       SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial column=(RemainingWordSeed369.value w column:F))) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (185562+index)) 2) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (179950+index)) 2) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial)
        (fun index => CapturedFullRelation58.rowAt (180205+index)) 2) ∧
      SharedScalarCanonical396.Rows
        (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial) := by
  obtain ⟨senderInitial,receiverInitial,initial,previous⟩ := IvkCanonicalConstruction391.legal_completed original c w legal
  exact ⟨senderInitial,receiverInitial,initial,previous,
    SharedScalarCanonical396.all_rows original c w initial senderInitial receiverInitial legal⟩

end ShielddSecurity.ScalarCanonicalConstruction397
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalConstruction397.legal_completed
#print axioms ShielddSecurity.ScalarCanonicalConstruction397.legal_completed
