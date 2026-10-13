import ShielddSecurity.UserPathFrame363
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathBounds364
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem smaller_values_checked : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.width<255 → entry.1.value≠1528 ∧ entry.1.value≠1766 ∧
      ¬(1531≤entry.1.value ∧ entry.1.value<1579) ∧ ¬(1769≤entry.1.value ∧ entry.1.value<1817))) = true := by decide +kernel

theorem smaller_values_outside (entry : WordHints210.Slot × Nat) (member : entry∈CapturedWordRoot213.words)
    (small : entry.1.width<255) :
    entry.1.value≠1528 ∧ entry.1.value≠1766 ∧
      ¬(1531≤entry.1.value ∧ entry.1.value<1579) ∧ ¬(1769≤entry.1.value ∧ entry.1.value<1817) :=
  (of_decide_eq_true (List.all_eq_true.mp smaller_values_checked entry member)) small

theorem number_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (entry : WordHints210.Slot × Nat) (member : entry∈CapturedWordRoot213.words) (small : entry.1.width<255) :
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
      (HighZeroSeed329.seed (UserWordSeed342.seed (UserPathSeed361.seed original w) w) w) w) c w) entry.1.value =
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
      (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) w) c w) entry.1.value := by
  have outside := smaller_values_outside entry member small
  unfold WordNaturalSeed297.numbers
  apply congrArg representation.value
  unfold HeaderRegistrySeed299.combined RegistryNaturalSeed298.seed HeaderRegistrySeed299.seed
    RegistryComparisonSeed318.seed HighZeroSeed329.seed FieldZeroSeed125.seeded UserWordSeed342.seed
  rw [UserPathSeed361.outside original w entry.1.value outside.1 outside.2.1 outside.2.2.1 outside.2.2.2]
end ShielddSecurity.UserPathBounds364

set_option pp.all true in
#check @ShielddSecurity.UserPathBounds364.smaller_values_checked
#print axioms ShielddSecurity.UserPathBounds364.smaller_values_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathBounds364.smaller_values_outside
#print axioms ShielddSecurity.UserPathBounds364.smaller_values_outside

set_option pp.all true in
#check @ShielddSecurity.UserPathBounds364.number_frame
#print axioms ShielddSecurity.UserPathBounds364.number_frame
