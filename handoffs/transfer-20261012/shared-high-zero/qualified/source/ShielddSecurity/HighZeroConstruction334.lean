import ShielddSecurity.SharedHighZeroRows333
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroConstruction334
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179023+index)) 3 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179287+index)) 3

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
      Rows (HighZeroCompletionFrame332.assignment original c w initial) ∧
      representation.value (HighZeroCompletionFrame332.assignment original c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HighZeroCompletionFrame332.assignment original c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,start,comparisons,pub,committed⟩ := ComparisonConstruction328.legal_completed
    (HighZeroSeed329.seed original w) c w legal remaining
  exact ⟨initial,rows,start,comparisons,
    ⟨SharedHighZeroRows333.first_rows original c w initial legal,
     SharedHighZeroRows333.second_rows original c w initial legal⟩,pub,committed⟩
end ShielddSecurity.HighZeroConstruction334

set_option pp.all true in
#check @ShielddSecurity.HighZeroConstruction334.Rows
#print axioms ShielddSecurity.HighZeroConstruction334.Rows

set_option pp.all true in
#check @ShielddSecurity.HighZeroConstruction334.legal_completed
#print axioms ShielddSecurity.HighZeroConstruction334.legal_completed
