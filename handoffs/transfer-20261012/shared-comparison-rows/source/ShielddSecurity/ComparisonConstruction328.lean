import ShielddSecurity.SharedComparisonBlocks327
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ComparisonConstruction328
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem WordHints210 LegalWordNormalization272

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178893+index)) 130 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179026+index)) 131 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179157+index)) 130 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179290+index)) 131

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed original w) c w) entry.1.value < 2^entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (SharedComparisonBlocks327.assignment original c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (SharedComparisonBlocks327.assignment original c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      Rows (SharedComparisonBlocks327.assignment original c w initial) ∧
      representation.value (SharedComparisonBlocks327.assignment original c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (SharedComparisonBlocks327.assignment original c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,start,pub,committed⟩ := RegistryComparisonConstruction319.legal_completed original c w legal remaining
  exact ⟨initial,rows,start,
    ⟨SharedComparisonBlocks327.first_high original c w initial legal,
     SharedComparisonBlocks327.first_low original c w initial legal,
     SharedComparisonBlocks327.second_high original c w initial legal,
     SharedComparisonBlocks327.second_low original c w initial legal⟩,pub,committed⟩
end ShielddSecurity.ComparisonConstruction328

set_option pp.all true in
#check @ShielddSecurity.ComparisonConstruction328.Rows
#print axioms ShielddSecurity.ComparisonConstruction328.Rows

set_option pp.all true in
#check @ShielddSecurity.ComparisonConstruction328.legal_completed
#print axioms ShielddSecurity.ComparisonConstruction328.legal_completed
