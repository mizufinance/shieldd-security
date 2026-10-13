import ShielddSecurity.CanonicalConstruction341
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserWordSeed342
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def values : List Nat := [1529,1530,1767,1768]
def value (w : TransferSem.Witness) (column : Nat) : Nat :=
  if column=1529 then w.sender.lifecycle
  else if column=1530 then w.sender.position
  else if column=1767 then w.receiver.lifecycle
  else if column=1768 then w.receiver.position
  else 0

def width (column : Nat) : Nat := if column=1529 ∨ column=1767 then 131 else 32

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column ∈ values then (value w column : F) else original column

theorem seed_value (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column ∈ values) : seed original w column = (value w column : F) := if_pos member

theorem seed_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (outside : column ∉ values) : seed original w column = original column := if_neg outside

theorem value_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (column : Nat) (member : column ∈ values) :
    value w column < 2^width column := by
  have sender := legal.2.1.2.1
  have receiver := legal.2.1.2.2.1
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact sender.2.2.2.2.2.2.1
  · exact sender.2.2.2.2.2.2.2.1
  · exact receiver.2.2.2.2.2.2.1
  · exact receiver.2.2.2.2.2.2.2.1

theorem width_below_field (column : Nat) : 2^width column < TransferCore.fieldModulus := by
  unfold width
  split <;> decide +kernel

theorem widths_checked : CapturedWordRoot213.words.all (fun entry =>
    decide (entry.1.value ∈ values → entry.1.width=width entry.1.value)) = true := by decide +kernel

theorem word_width (entry : WordHints210.Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (user : entry.1.value ∈ values) : entry.1.width=width entry.1.value :=
  (of_decide_eq_true ((List.all_eq_true.mp widths_checked) entry member)) user

theorem combined_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (column : Nat) (member : column ∈ values) :
    HeaderRegistrySeed299.combined
      (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (seed original w) w) w) c w column = (value w column : F) := by
  have lower : 1374 < column := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide
  have upper : column < 2000 := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide
  unfold HeaderRegistrySeed299.combined
  rw [RegistryNaturalSeed298.untouched _ w.registry column (by
    simp only [RegistryNaturalSeed298.fixedColumns,List.mem_cons,List.not_mem_nil,or_false]
    omega) (by omega),HeaderRegistrySeed299.seed_outside _ c w column (by omega) (by omega),
    RegistryComparisonSeed318.seed_outside _ w column (by
      simp only [RegistryComparisonSeed318.written,List.mem_cons,List.not_mem_nil,or_false]
      omega),HighZeroSeed329.outside _ w column (Or.inr (by omega)) (Or.inr (by omega)),seed_value original w column member]

theorem natural_bound (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (entry : WordHints210.Slot × Nat)
    (member : entry ∈ CapturedWordRoot213.words) (user : entry.1.value ∈ values) :
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined
      (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (seed original w) w) w) c w) entry.1.value < 2^entry.1.width := by
  have bound := value_bound c w legal entry.1.value user
  rw [word_width entry member user]
  change representation.value (HeaderRegistrySeed299.combined
    (RegistryComparisonSeed318.seed (HighZeroSeed329.seed (seed original w) w) w) c w entry.1.value) < _
  rw [combined_value original c w entry.1.value user,
    RegistryNaturalSeed298.represented_nat _ (lt_trans bound (width_below_field entry.1.value))]
  exact bound
end ShielddSecurity.UserWordSeed342

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.values
#print axioms ShielddSecurity.UserWordSeed342.values

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.value
#print axioms ShielddSecurity.UserWordSeed342.value

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.width
#print axioms ShielddSecurity.UserWordSeed342.width

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.seed
#print axioms ShielddSecurity.UserWordSeed342.seed

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.seed_value
#print axioms ShielddSecurity.UserWordSeed342.seed_value

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.seed_outside
#print axioms ShielddSecurity.UserWordSeed342.seed_outside

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.value_bound
#print axioms ShielddSecurity.UserWordSeed342.value_bound

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.width_below_field
#print axioms ShielddSecurity.UserWordSeed342.width_below_field

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.widths_checked
#print axioms ShielddSecurity.UserWordSeed342.widths_checked

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.word_width
#print axioms ShielddSecurity.UserWordSeed342.word_width

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.combined_value
#print axioms ShielddSecurity.UserWordSeed342.combined_value

set_option pp.all true in
#check @ShielddSecurity.UserWordSeed342.natural_bound
#print axioms ShielddSecurity.UserWordSeed342.natural_bound
