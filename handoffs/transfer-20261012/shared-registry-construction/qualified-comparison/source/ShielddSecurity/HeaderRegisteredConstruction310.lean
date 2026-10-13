import ShielddSecurity.RegisteredConstructorFrame309
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HeaderRegisteredConstruction310
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309

def numbers (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) : Nat → Nat :=
  WordNaturalSeed297.numbers (prepared original c w)
def fallback (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) : Nat → Bool :=
  LegalAliasMeanings276.fallback (numbers original c w) (ZeroHintWordFrame303.flags (prepared original c w))
def completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : Nat → F :=
  SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
    (normalized (numbers original c w)) (fallback original c w)

theorem number_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) :
    numbers original c w entry.1.value =
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined original c w) entry.1.value :=
  congrArg representation.value (word_value original c w entry member)

theorem smaller_bounds (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined original c w) entry.1.value < 2 ^ entry.1.width) :
    ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → numbers original c w entry.1.value < 2 ^ entry.1.width := by
  intro entry member outside small
  rw [number_frame original c w entry member]
  exact HeaderSharedConstruction300.smaller_bounds original c w legal remaining entry member outside small

theorem registered_assertions (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (completed original c w initial)
      CapturedRegisteredAudit70.block.actual 35 := by
  have stage := SharedRegisteredGeneral308.completed_assertions
    (CapturedFourSubgroupSeed89.seeded (HeaderRegisteredLegality307.base original c w) initial)
    (normalized (numbers original c w)) (fallback original c w)
    ((CapturedFourSubgroupSeed89.seeded_outside _ initial 0 (by decide)).trans
      (HeaderRegisteredLegality307.base_zero original c w))
    (fallback_agrees (HeaderRegisteredLegality307.base original c w) initial (numbers original c w))
    (by rw [CapturedFourSubgroupSeed89.seeded_outside _ initial 10 (by decide)]
        exact HeaderRegisteredLegality307.base_control original c w)
    (group_guards _ initial (HeaderRegisteredLegality307.legal_guards original c w legal))
  change CompilerAssertionBlock51.SatisfiesAt
    (SharedWordWitness221.completed
      (CapturedRegisteredHints72.seeded (CapturedFourSubgroupSeed89.seeded
        (HeaderRegisteredLegality307.base original c w) initial))
      (normalized (numbers original c w)) (fallback original c w)) _ _ at stage
  rw [commute] at stage
  exact stage

theorem public_meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    representation.value (completed original c w initial 1) =
      (crypto c).hash .transferStatement (publicFields (crypto c) w) := by
  have pub := SharedPublicFrame301.completed_declared_public
    (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
    (normalized (numbers original c w)) (fallback original c w)
  have group := CapturedFourSubgroupSeed89.seeded_outside (prepared original c w) initial 22737 (by decide)
  have frame := prepared_outside original c w 22737 (by decide) (by constructor <;> decide)
  exact (congrArg representation.value (pub.trans (group.trans frame))).trans
    ((congrArg representation.value (HeaderRegistrySeed299.public_input_same original c w)).trans
      (HeaderRegistrySeed299.claim_preserved original c w))

theorem committed_meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    representation.value (completed original c w initial 2) = w.blinding := by
  have linked := (CapturedFullRelation58.candidate_links
    (SharedWordWitness221.seeded
      (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
      (normalized (numbers original c w)) (fallback original c w))).2.1
  have word := RegistrySeedFrame265.completed_frame
    (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
    (normalized (numbers original c w)) (fallback original c w) 9 (by constructor <;> omega)
  have group := CapturedFourSubgroupSeed89.seeded_outside (prepared original c w) initial 9 (by decide)
  have frame := prepared_outside original c w 9 (by decide) (by constructor <;> decide)
  have header := (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.2.1
  exact (congrArg representation.value (linked.trans (word.trans (group.trans (frame.trans header))))).trans
    (RegistryNaturalSeed298.represented_nat _ (lt_trans (HeaderRegistrySeed299.legal_blinding c w legal)
      HeaderRegistrySeed299.scalar_below_field))

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined original c w) entry.1.value < 2 ^ entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (completed original c w initial) ∧
      (∀ group, Satisfies (completed original c w initial)
        (CapturedFourSubgroupConstructor88.originalRows group)) ∧
      (∃ row, CapturedFullRelation58.rowAt 178117 = some row ∧
        Square (eval (completed original c w initial) row.a) (eval (completed original c w initial) row.b)) ∧
      CompilerAssertionBlock51.SatisfiesAt (completed original c w initial)
        CapturedRegisteredAudit70.block.actual 35 ∧
      representation.value (completed original c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (completed original c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,groups,anchor⟩ := WordNaturalSeed297.legal_completed c (prepared original c w)
    (ZeroHintWordFrame303.flags (prepared original c w)) (prepared_zero original c w)
    (smaller_bounds original c w legal remaining) w legal.2.1.1
    ((registry_frame original c w).trans (HeaderRegistrySeed299.recover_registry original c w legal.1))
    ((congrArg representation.value (prepared_outside original c w 4 (by decide) (by constructor <;> decide))).trans
      (HeaderSharedConstruction300.anchor_meaning original c w legal))
  exact ⟨initial,rows,groups,anchor,registered_assertions original c w initial legal.2.1.1,
    public_meaning original c w initial,committed_meaning original c w initial legal⟩
end ShielddSecurity.HeaderRegisteredConstruction310

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.numbers
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.numbers

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.fallback
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.fallback

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.completed
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.completed

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.number_frame
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.number_frame

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.smaller_bounds
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.smaller_bounds

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.registered_assertions
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.registered_assertions

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.public_meaning
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.public_meaning

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.committed_meaning
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.committed_meaning

set_option pp.all true in
#check @ShielddSecurity.HeaderRegisteredConstruction310.legal_completed
#print axioms ShielddSecurity.HeaderRegisteredConstruction310.legal_completed
