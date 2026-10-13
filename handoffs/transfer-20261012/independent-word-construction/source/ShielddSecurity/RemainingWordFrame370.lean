import ShielddSecurity.RemainingWordSeed369
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RemainingWordFrame370
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem prepared_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (column : Nat) (auth : column∈RemainingWordSeed369.values) :
    HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
      (HighZeroSeed329.seed (UserWordSeed342.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w) w) c w column =
      (RemainingWordSeed369.value w column:F) := by
  have limits : 3766<column ∧ column<22737 := by
    simp only [RemainingWordSeed369.values,List.mem_cons,List.not_mem_nil,or_false] at auth
    rcases auth with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> decide
  unfold HeaderRegistrySeed299.combined
  rw [RegistryNaturalSeed298.untouched _ w.registry column (by
    simp only [RegistryNaturalSeed298.fixedColumns,List.mem_cons,List.not_mem_nil,or_false]; omega) (by omega),
    HeaderRegistrySeed299.seed_outside _ c w column (by omega) (by omega),
    RegistryComparisonSeed318.seed_outside _ w column (by
      simp only [RegistryComparisonSeed318.written,List.mem_cons,List.not_mem_nil,or_false]; omega),
    HighZeroSeed329.outside _ w column (Or.inr (by omega)) (Or.inr (by omega)),
    UserWordSeed342.seed_outside _ w column (by
      simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false]; omega),
    AuthScalarSeed366.seed_outside _ w column (by
      simp only [AuthScalarSeed366.values,List.mem_cons,List.not_mem_nil,or_false]; omega),
    RemainingWordSeed369.seed_value original w column auth]

theorem natural_bound (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (entry : WordHints210.Slot × Nat)
    (member : entry∈CapturedWordRoot213.words) (auth : entry.1.value∈RemainingWordSeed369.values) :
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
      (HighZeroSeed329.seed (UserWordSeed342.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w) w) c w) entry.1.value < 2^entry.1.width := by
  have bound := RemainingWordSeed369.value_bound c w legal entry.1.value auth
  rw [RemainingWordSeed369.word_width entry member auth]
  change representation.value (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
    (HighZeroSeed329.seed (UserWordSeed342.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w) w) w) c w entry.1.value) < _
  rw [prepared_value original c w entry.1.value auth,
    RegistryNaturalSeed298.represented_nat _ (lt_trans bound (RemainingWordSeed369.width_below_field entry.1.value))]
  exact bound
end ShielddSecurity.RemainingWordFrame370

set_option pp.all true in
#check @ShielddSecurity.RemainingWordFrame370.prepared_value
#print axioms ShielddSecurity.RemainingWordFrame370.prepared_value

set_option pp.all true in
#check @ShielddSecurity.RemainingWordFrame370.natural_bound
#print axioms ShielddSecurity.RemainingWordFrame370.natural_bound
