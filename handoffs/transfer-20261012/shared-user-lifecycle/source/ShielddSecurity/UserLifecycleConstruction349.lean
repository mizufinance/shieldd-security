import ShielddSecurity.SharedUserLifecycle348
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserLifecycleConstruction349
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues → entry.1.value ∉ UserWordSeed342.values →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) w) c w) entry.1.value < 2^entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      ComparisonConstruction328.Rows (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial) ∧
      HighZeroConstruction334.Rows (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial)
        (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 ∧
      SharedCanonicalRows340.Rows (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial) ∧
      SharedUserLifecycle348.Rows (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial) ∧
      representation.value (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,start,comparisons,zeros,gap,canonical,pub,committed⟩ :=
    UserWordConstruction343.legal_completed original c w legal remaining
  exact ⟨initial,rows,start,comparisons,zeros,gap,canonical,
    SharedUserLifecycle348.all_rows original c w initial legal,pub,committed⟩

end ShielddSecurity.UserLifecycleConstruction349
set_option pp.all true in
#check @ShielddSecurity.UserLifecycleConstruction349.legal_completed
#print axioms ShielddSecurity.UserLifecycleConstruction349.legal_completed
