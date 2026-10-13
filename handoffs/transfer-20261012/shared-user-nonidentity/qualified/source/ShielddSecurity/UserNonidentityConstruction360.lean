import ShielddSecurity.UserSubgroupConstruction357
import ShielddSecurity.SharedUserNonidentity359
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserNonidentityConstruction360
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues → entry.1.value ∉ UserWordSeed342.values →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) w) c w) entry.1.value < 2^entry.1.width) :
    ∃ senderInitial : Fin 3 → Group.Point F, ∃ receiverInitial : Fin 3 → Group.Point F,
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      ComparisonConstruction328.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      HighZeroConstruction334.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial)
        (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 ∧
      SharedCanonicalRows340.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      SharedUserLifecycle348.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      UserSubgroupCapture355.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      CapturedUserNonidentity358.Rows (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial 2) = w.blinding := by
  obtain ⟨senderInitial,receiverInitial,initial,rows,start,comparisons,zeros,gap,canonical,lifecycles,subgroups,pub,committed⟩ :=
    UserSubgroupConstruction357.legal_completed original c w legal remaining
  exact ⟨senderInitial,receiverInitial,initial,rows,start,comparisons,zeros,gap,canonical,lifecycles,subgroups,
    SharedUserNonidentity359.all_rows original c w legal initial senderInitial receiverInitial,pub,committed⟩

end ShielddSecurity.UserNonidentityConstruction360
set_option pp.all true in
#check @ShielddSecurity.UserNonidentityConstruction360.legal_completed
#print axioms ShielddSecurity.UserNonidentityConstruction360.legal_completed
