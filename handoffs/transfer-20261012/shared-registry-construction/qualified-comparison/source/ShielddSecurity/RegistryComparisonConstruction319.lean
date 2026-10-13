import ShielddSecurity.RegistryComparisonSeed318
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryComparisonConstruction319
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem WordHints210 LegalWordNormalization272

theorem remaining_bounds (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed original w) c w) entry.1.value < 2^entry.1.width) :
    ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed original w) c w) entry.1.value < 2^entry.1.width := by
  intro entry member outside small unknown
  by_cases selected : entry.1.value ∈ RegistryComparisonSeed318.comparisonValues
  · exact RegistryComparisonSeed318.natural_bounds original c w legal entry member selected
  · exact remaining entry member outside small unknown selected

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      entry.1.value ∉ RegistryComparisonSeed318.comparisonValues →
      WordNaturalSeed297.numbers
        (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed original w) c w) entry.1.value < 2^entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows
        (HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt
        (HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      representation.value (HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial 2) = w.blinding :=
  SharedRegistryFirst165317.legal_completed (RegistryComparisonSeed318.seed original w) c w legal
    (remaining_bounds original c w legal.2.1.1 remaining)
end ShielddSecurity.RegistryComparisonConstruction319

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonConstruction319.remaining_bounds
#print axioms ShielddSecurity.RegistryComparisonConstruction319.remaining_bounds

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonConstruction319.legal_completed
#print axioms ShielddSecurity.RegistryComparisonConstruction319.legal_completed
