import ShielddSecurity.RegistryWordBits322
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompletedComparisonValues323
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

theorem word_value_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (outside : ¬ Alias entry.1.value) :
    HeaderRegisteredConstruction310.completed original c w initial entry.1.value = prepared original c w entry.1.value := by
  let base := CapturedFourSubgroupSeed89.seeded (prepared original c w) initial
  let seeded := SharedWordWitness221.seeded base (normalized (numbers original c w)) (fallback original c w)
  have bounds := (CapturedWordRoot213.originals entry member).2
  change CapturedFullRelation58.candidate seeded entry.1.value = _
  exact (SharedRegisteredGeneral308.candidate_original seeded entry.1.value bounds.1 bounds.2).trans
    ((BooleanHints207.seeded_outside base _ _ entry.1.value (LegalWordEncoding278.seed_outside entry member outside)).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial entry.1.value (LegalSharedRows271.values_outside entry member)))

theorem comparison_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (selected : entry.1.value ∈ RegistryComparisonSeed318.comparisonValues) :
    HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial entry.1.value =
      (RegistryComparisonSeed318.difference w entry.1.value : F) := by
  have outside : ¬ Alias entry.1.value := by
    simp only [RegistryComparisonSeed318.comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> simp only [Alias] <;> omega
  have frame := word_value_frame (RegistryComparisonSeed318.seed original w) c w initial entry member outside
  have hints : entry.1.value < 49 ∨ 135 ≤ entry.1.value := by
    simp only [RegistryComparisonSeed318.comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> omega
  have links : entry.1.value ≠ copy ∧ entry.1.value ≠ 1 ∧ entry.1.value ≠ 2 := by
    simp only [RegistryComparisonSeed318.comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> norm_num [copy] <;> omega
  exact frame.trans ((prepared_outside (RegistryComparisonSeed318.seed original w) c w entry.1.value hints links).trans
    (RegistryComparisonSeed318.combined_value original c w entry.1.value selected))

theorem first_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial 982 =
      (RegistryComparisonSeed318.difference w 982 : F) :=
  comparison_value original c w initial (CapturedWordSlots211B001.W06.slot,CapturedWordSlots211B001.W06.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))) (by decide)

theorem first_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial 1113 =
      (RegistryComparisonSeed318.difference w 1113 : F) :=
  comparison_value original c w initial (CapturedWordSlots211B001.W07.slot,CapturedWordSlots211B001.W07.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))) (by decide)

theorem second_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial 1243 =
      (RegistryComparisonSeed318.difference w 1243 : F) :=
  comparison_value original c w initial (CapturedWordSlots211B002.W08.slot,CapturedWordSlots211B002.W08.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (by decide)

theorem second_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial 1374 =
      (RegistryComparisonSeed318.difference w 1374 : F) :=
  comparison_value original c w initial (CapturedWordSlots211B002.W09.slot,CapturedWordSlots211B002.W09.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))) (by decide)

end ShielddSecurity.CompletedComparisonValues323

set_option pp.all true in
#check @ShielddSecurity.CompletedComparisonValues323.word_value_frame
#print axioms ShielddSecurity.CompletedComparisonValues323.word_value_frame

set_option pp.all true in
#check @ShielddSecurity.CompletedComparisonValues323.comparison_value
#print axioms ShielddSecurity.CompletedComparisonValues323.comparison_value

set_option pp.all true in
#check @ShielddSecurity.CompletedComparisonValues323.first_high
#print axioms ShielddSecurity.CompletedComparisonValues323.first_high

set_option pp.all true in
#check @ShielddSecurity.CompletedComparisonValues323.first_low
#print axioms ShielddSecurity.CompletedComparisonValues323.first_low

set_option pp.all true in
#check @ShielddSecurity.CompletedComparisonValues323.second_high
#print axioms ShielddSecurity.CompletedComparisonValues323.second_high

set_option pp.all true in
#check @ShielddSecurity.CompletedComparisonValues323.second_low
#print axioms ShielddSecurity.CompletedComparisonValues323.second_low
