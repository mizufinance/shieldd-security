import ShielddSecurity.UserWordSeed342
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserWordConstruction343
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
      representation.value (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial 2) = w.blinding := by
  have bounds : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) w) c w) entry.1.value < 2^entry.1.width := by
    intro entry member outsideAlias small known comparisons
    by_cases user : entry.1.value ∈ UserWordSeed342.values
    · exact UserWordSeed342.natural_bound original c w legal entry member user
    · exact remaining entry member outsideAlias small known comparisons user
  exact CanonicalConstruction341.legal_completed (UserWordSeed342.seed original w) c w legal bounds

end ShielddSecurity.UserWordConstruction343
set_option pp.all true in
#check @ShielddSecurity.UserWordConstruction343.legal_completed
#print axioms ShielddSecurity.UserWordConstruction343.legal_completed
