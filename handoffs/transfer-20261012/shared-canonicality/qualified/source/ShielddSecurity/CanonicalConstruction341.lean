import ShielddSecurity.GapConstruction339
import ShielddSecurity.SharedCanonicalRows340
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalConstruction341
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) entry.1.value < 2^entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (HighZeroCompletionFrame332.assignment original c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (HighZeroCompletionFrame332.assignment original c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      ComparisonConstruction328.Rows (HighZeroCompletionFrame332.assignment original c w initial) ∧
      HighZeroConstruction334.Rows (HighZeroCompletionFrame332.assignment original c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (HighZeroCompletionFrame332.assignment original c w initial)
        (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 ∧
      SharedCanonicalRows340.Rows (HighZeroCompletionFrame332.assignment original c w initial) ∧
      representation.value (HighZeroCompletionFrame332.assignment original c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HighZeroCompletionFrame332.assignment original c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,start,comparisons,zeros,gap,pub,committed⟩ := GapConstruction339.legal_completed original c w legal remaining
  exact ⟨initial,rows,start,comparisons,zeros,gap,SharedCanonicalRows340.all_rows original c w initial legal,pub,committed⟩
end ShielddSecurity.CanonicalConstruction341
set_option pp.all true in
#check @ShielddSecurity.CanonicalConstruction341.legal_completed
#print axioms ShielddSecurity.CanonicalConstruction341.legal_completed
