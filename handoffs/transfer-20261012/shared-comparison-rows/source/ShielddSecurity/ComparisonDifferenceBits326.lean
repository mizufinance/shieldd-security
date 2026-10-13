import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ComparisonDifferenceBits326
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

theorem difference_canonical (c : Crypto) (w : TransferSem.Witness) (legal : RegistrySem (crypto c) w)
    (column : Nat) (selected : column ∈ RegistryComparisonSeed318.comparisonValues) :
    RegistryComparisonSeed318.difference w column < TransferCore.fieldModulus := by
  have bounds := RegistryComparisonSeed318.difference_bounds c w legal
  simp only [RegistryComparisonSeed318.comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at selected
  rcases selected with first | second | third | fourth
  · rw [first]; exact lt_trans bounds.1 RegistryComparisonSeed318.high_below_field
  · rw [second]; exact lt_trans bounds.2.1 RegistryComparisonSeed318.low_below_field
  · rw [third]; exact lt_trans bounds.2.2.1 RegistryComparisonSeed318.high_below_field
  · rw [fourth]; exact lt_trans bounds.2.2.2 RegistryComparisonSeed318.low_below_field

theorem number_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem (crypto c) w) (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (selected : entry.1.value ∈ RegistryComparisonSeed318.comparisonValues) :
    numbers (RegistryComparisonSeed318.seed original w) c w entry.1.value = RegistryComparisonSeed318.difference w entry.1.value :=
  (HeaderRegisteredConstruction310.number_frame (RegistryComparisonSeed318.seed original w) c w entry member).trans
    ((congrArg representation.value (RegistryComparisonSeed318.combined_value original c w entry.1.value selected)).trans
      (RegistryNaturalSeed298.represented_nat _ (difference_canonical c w legal entry.1.value selected)))

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w)
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (selected : entry.1.value ∈ RegistryComparisonSeed318.comparisonValues) :
    ∀ index < entry.1.width,
      HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial (entry.1.start+index) =
        if (encodeBits entry.1.width (RegistryComparisonSeed318.difference w entry.1.value))[index]?.getD false then 1 else 0 := by
  have outside : ¬Alias entry.1.value := by
    simp only [RegistryComparisonSeed318.comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> simp only [Alias] <;> omega
  have fixed : normalized (numbers (RegistryComparisonSeed318.seed original w) c w) entry.1.value =
      RegistryComparisonSeed318.difference w entry.1.value :=
    (LegalWordNormalization272.fixed _ entry.1.value outside).trans (number_value original c w legal entry member selected)
  intro index bound
  have point := SharedWordLimbMeaning321.encoded_point
    (CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed original w) c w) initial)
    (normalized (numbers (RegistryComparisonSeed318.seed original w) c w)) (fallback (RegistryComparisonSeed318.seed original w) c w)
    (LegalWordNormalization272.coherent _) entry member index bound
  simpa only [fixed] using point

theorem first_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    ∀ index < 127, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial (983+index) =
      if (encodeBits 127 (BoundedLimbComparison119.difference 127 (RegistryComparisonSeed318.high w.asset) (RegistryComparisonSeed318.high w.registry.value)))[index]?.getD false then 1 else 0 :=
  bits original c w initial legal (CapturedWordSlots211B001.W06.slot,CapturedWordSlots211B001.W06.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))) (by decide)

theorem first_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    ∀ index < 128, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial (1114+index) =
      if (encodeBits 128 (BoundedLimbComparison119.difference 128 (RegistryComparisonSeed318.low w.asset) (RegistryComparisonSeed318.low w.registry.value)))[index]?.getD false then 1 else 0 :=
  bits original c w initial legal (CapturedWordSlots211B001.W07.slot,CapturedWordSlots211B001.W07.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))) (by decide)

theorem second_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    ∀ index < 127, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial (1244+index) =
      if (encodeBits 127 (BoundedLimbComparison119.difference 127 (RegistryComparisonSeed318.high w.registry.nextValue) (RegistryComparisonSeed318.high w.asset)))[index]?.getD false then 1 else 0 :=
  bits original c w initial legal (CapturedWordSlots211B002.W08.slot,CapturedWordSlots211B002.W08.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (by decide)

theorem second_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    ∀ index < 128, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial (1375+index) =
      if (encodeBits 128 (BoundedLimbComparison119.difference 128 (RegistryComparisonSeed318.low w.registry.nextValue) (RegistryComparisonSeed318.low w.asset)))[index]?.getD false then 1 else 0 :=
  bits original c w initial legal (CapturedWordSlots211B002.W09.slot,CapturedWordSlots211B002.W09.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))) (by decide)

end ShielddSecurity.ComparisonDifferenceBits326

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.difference_canonical
#print axioms ShielddSecurity.ComparisonDifferenceBits326.difference_canonical

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.number_value
#print axioms ShielddSecurity.ComparisonDifferenceBits326.number_value

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.bits
#print axioms ShielddSecurity.ComparisonDifferenceBits326.bits

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.first_high
#print axioms ShielddSecurity.ComparisonDifferenceBits326.first_high

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.first_low
#print axioms ShielddSecurity.ComparisonDifferenceBits326.first_low

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.second_high
#print axioms ShielddSecurity.ComparisonDifferenceBits326.second_high

set_option pp.all true in
#check @ShielddSecurity.ComparisonDifferenceBits326.second_low
#print axioms ShielddSecurity.ComparisonDifferenceBits326.second_low
