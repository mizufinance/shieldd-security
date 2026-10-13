import ShielddSecurity.AuthScalarFrame367
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthScalarConstruction368
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues → entry.1.value ∉ UserWordSeed342.values →
      entry.1.value ∉ AuthScalarSeed366.values →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed (AuthScalarSeed366.seed original w) w) w) w) c w) entry.1.value < 2^entry.1.width) :
    ∃ senderInitial : Fin 3 → Group.Point F, ∃ receiverInitial : Fin 3 → Group.Point F,
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      ComparisonConstruction328.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      HighZeroConstruction334.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 ∧
      SharedCanonicalRows340.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      SharedUserLifecycle348.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      UserSubgroupCapture355.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      CapturedUserNonidentity358.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial) ∧
      (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial 1528=(w.sender.rnkCommitment:F) ∧
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial 1766=(w.receiver.rnkCommitment:F)) ∧
      (∀ (level : Fin 16) (slot : Fin 3),
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial (1531+3*level.val+slot.val)=(w.sender.siblings level slot:F) ∧
       UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial (1769+3*level.val+slot.val)=(w.receiver.siblings level slot:F)) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed (AuthScalarSeed366.seed original w) w) w senderInitial receiverInitial) c w initial 2) = w.blinding := by
  have bounds : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues → entry.1.value ∉ UserWordSeed342.values →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed (AuthScalarSeed366.seed original w) w) w) w) c w) entry.1.value < 2^entry.1.width := by
    intro entry member outsideAlias small known comparisons user
    by_cases auth : entry.1.value∈AuthScalarSeed366.values
    · exact AuthScalarFrame367.natural_bound original c w legal entry member auth
    · exact remaining entry member outsideAlias small known comparisons user auth
  exact UserPathConstruction365.legal_completed (AuthScalarSeed366.seed original w) c w legal bounds

end ShielddSecurity.AuthScalarConstruction368
set_option pp.all true in
#check @ShielddSecurity.AuthScalarConstruction368.legal_completed
#print axioms ShielddSecurity.AuthScalarConstruction368.legal_completed
