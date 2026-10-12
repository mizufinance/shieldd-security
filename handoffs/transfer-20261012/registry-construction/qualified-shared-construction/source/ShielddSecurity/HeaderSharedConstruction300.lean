import ShielddSecurity.HeaderRegistrySeed299
import ShielddSecurity.SharedPublicFrame301
import ShielddSecurity.SharedCompletedLinks302
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HeaderSharedConstruction300
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open PoseidonNatural192 TransferSem WordHints210 LegalWordNormalization272

def knownValues : List Nat := [7,9,21,34,135]

theorem widths_checked : CapturedWordRoot213.words.all (fun entry => decide
    ((entry.1.value = 7 → entry.1.width = 64) ∧
     (entry.1.value = 9 → entry.1.width = 252) ∧
     (entry.1.value = 21 → entry.1.width = 128) ∧
     (entry.1.value = 34 → entry.1.width = 64) ∧
     (entry.1.value = 135 → entry.1.width = 32))) = true := by decide +kernel

theorem daily_limit_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : w.registry.dailyLimit < 2 ^ 128 :=
  legal.2.1.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1

theorem daily_word_bound (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w) 21 < 2 ^ 128 := by
  have equal := congrArg (fun leaf : AssetLeaf => leaf.dailyLimit)
    (HeaderRegistrySeed299.recover_registry base c w legal.1)
  change representation.value (HeaderRegistrySeed299.combined base c w 21) < 2 ^ 128
  change representation.value (HeaderRegistrySeed299.combined base c w 21) = w.registry.dailyLimit at equal
  rw [equal]
  exact daily_limit_bound c w legal

theorem smaller_bounds (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ knownValues →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w) entry.1.value < 2 ^ entry.1.width) :
    ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w) entry.1.value < 2 ^ entry.1.width := by
  intro entry member outside small
  have widths := of_decide_eq_true ((List.all_eq_true.mp widths_checked) entry member)
  by_cases time : entry.1.value = 7
  · rw [widths.1 time, time]
    exact HeaderRegistrySeed299.time_word_bound base c w legal
  by_cases blinding : entry.1.value = 9
  · rw [widths.2.1 blinding, blinding]
    exact HeaderRegistrySeed299.blinding_word_bound base c w legal
  by_cases limit : entry.1.value = 21
  · rw [widths.2.2.1 limit, limit]
    exact daily_word_bound base c w legal
  by_cases epoch : entry.1.value = 34
  · rw [widths.2.2.2.1 epoch, epoch]
    exact RegistryNaturalSeed298.epoch_word_bound (crypto c) w (HeaderRegistrySeed299.seed base c w)
      (HeaderRegistrySeed299.canonical_registry w legal.1) legal.2.1.1
  by_cases position : entry.1.value = 135
  · rw [widths.2.2.2.2 position, position]
    exact RegistryNaturalSeed298.position_word_bound (crypto c) w (HeaderRegistrySeed299.seed base c w)
      (HeaderRegistrySeed299.canonical_registry w legal.1) legal.2.1.1
  exact remaining entry member outside small (by simp [knownValues,time,blinding,limit,epoch,position])

def completed (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (old : Nat → Bool) : Nat → F :=
  SharedWordWitness221.completed
    (CapturedFourSubgroupSeed89.seeded (HeaderRegistrySeed299.combined base c w) initial)
    (normalized (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)))
    (LegalAliasMeanings276.fallback (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)) old)

theorem public_meaning (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (old : Nat → Bool) :
    representation.value (completed base c w initial old 1) =
      (crypto c).hash .transferStatement (publicFields (crypto c) w) := by
  have pub := SharedPublicFrame301.completed_declared_public
    (CapturedFourSubgroupSeed89.seeded (HeaderRegistrySeed299.combined base c w) initial)
    (normalized (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)))
    (LegalAliasMeanings276.fallback (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)) old)
  have frame := CapturedFourSubgroupSeed89.seeded_outside (HeaderRegistrySeed299.combined base c w)
    initial 22737 (by decide)
  exact (congrArg representation.value (pub.trans frame)).trans
    ((congrArg representation.value (HeaderRegistrySeed299.public_input_same base c w)).trans
      (HeaderRegistrySeed299.claim_preserved base c w))

theorem committed_meaning (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (old : Nat → Bool)
    (legal : TransferSem.TransferSem (crypto c) w) :
    representation.value (completed base c w initial old 2) = w.blinding := by
  have linked := (CapturedFullRelation58.candidate_links
    (SharedWordWitness221.seeded
      (CapturedFourSubgroupSeed89.seeded (HeaderRegistrySeed299.combined base c w) initial)
      (normalized (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)))
      (LegalAliasMeanings276.fallback (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)) old))).2.1
  have word := RegistrySeedFrame265.completed_frame
    (CapturedFourSubgroupSeed89.seeded (HeaderRegistrySeed299.combined base c w) initial)
    (normalized (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)))
    (LegalAliasMeanings276.fallback (WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w)) old) 9
    (by constructor <;> omega)
  have subgroup := CapturedFourSubgroupSeed89.seeded_outside (HeaderRegistrySeed299.combined base c w)
    initial 9 (by decide)
  have header := (HeaderRegistrySeed299.original_headers base c w).2.2.2.2.2.2.2.2.2.1
  exact (congrArg representation.value (linked.trans (word.trans (subgroup.trans header)))).trans
    (RegistryNaturalSeed298.represented_nat _ (lt_trans (HeaderRegistrySeed299.legal_blinding c w legal)
      HeaderRegistrySeed299.scalar_below_field))

theorem anchor_meaning (base : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    representation.value (HeaderRegistrySeed299.combined base c w 4) = w.assetAnchor := by
  rw [(HeaderRegistrySeed299.original_headers base c w).2.2.2.2.1]
  apply RegistryNaturalSeed298.represented_nat
  exact legal.1 _ (by simp)

theorem legal_completed (base : Nat → F) (c : Crypto) (w : TransferSem.Witness) (old : Nat → Bool)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ knownValues →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined base c w) entry.1.value < 2 ^ entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (completed base c w initial old) ∧
      (∀ group, Satisfies (completed base c w initial old)
        (CapturedFourSubgroupConstructor88.originalRows group)) ∧
      (∃ row, CapturedFullRelation58.rowAt 178117 = some row ∧
        Square (eval (completed base c w initial old) row.a) (eval (completed base c w initial old) row.b)) ∧
      representation.value (completed base c w initial old 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (completed base c w initial old 2) = w.blinding := by
  obtain ⟨initial, rows, groups, anchor⟩ := WordNaturalSeed297.legal_completed c
    (HeaderRegistrySeed299.combined base c w) old
    (HeaderRegistrySeed299.original_headers base c w).1 (smaller_bounds base c w legal remaining) w
    legal.2.1.1 (HeaderRegistrySeed299.recover_registry base c w legal.1) (anchor_meaning base c w legal)
  exact ⟨initial, rows, groups, anchor, public_meaning base c w initial old,
    committed_meaning base c w initial old legal⟩
end ShielddSecurity.HeaderSharedConstruction300


set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.knownValues
#print axioms ShielddSecurity.HeaderSharedConstruction300.knownValues

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.widths_checked
#print axioms ShielddSecurity.HeaderSharedConstruction300.widths_checked

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.daily_limit_bound
#print axioms ShielddSecurity.HeaderSharedConstruction300.daily_limit_bound

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.daily_word_bound
#print axioms ShielddSecurity.HeaderSharedConstruction300.daily_word_bound

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.smaller_bounds
#print axioms ShielddSecurity.HeaderSharedConstruction300.smaller_bounds

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.completed
#print axioms ShielddSecurity.HeaderSharedConstruction300.completed

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.public_meaning
#print axioms ShielddSecurity.HeaderSharedConstruction300.public_meaning

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.committed_meaning
#print axioms ShielddSecurity.HeaderSharedConstruction300.committed_meaning

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.anchor_meaning
#print axioms ShielddSecurity.HeaderSharedConstruction300.anchor_meaning

set_option pp.all true in
#check @ShielddSecurity.HeaderSharedConstruction300.legal_completed
#print axioms ShielddSecurity.HeaderSharedConstruction300.legal_completed
