import ShielddSecurity.SharedRegistryFirst165317
import ShielddSecurity.HighBitMeaning122
import ShielddSecurity.BoundedLimbComparison119
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryComparisonSeed318
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def comparisonValues : List Nat := [982,1113,1243,1374]
def written : List Nat := [981,982,1112,1113,1242,1243,1373,1374]
def high (n : Nat) : Nat := n / 2^128
def low (n : Nat) : Nat := n % 2^128

def difference (w : TransferSem.Witness) (column : Nat) : Nat :=
  if column=982 then BoundedLimbComparison119.difference 127 (high w.asset) (high w.registry.value)
  else if column=1113 then BoundedLimbComparison119.difference 128 (low w.asset) (low w.registry.value)
  else if column=1243 then BoundedLimbComparison119.difference 127 (high w.registry.nextValue) (high w.asset)
  else if column=1374 then BoundedLimbComparison119.difference 128 (low w.registry.nextValue) (low w.asset)
  else 0

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column ∈ comparisonValues then (difference w column : F)
  else if column=981 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (high w.asset) (high w.registry.value))
  else if column=1112 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (low w.asset) (low w.registry.value))
  else if column=1242 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (high w.registry.nextValue) (high w.asset))
  else if column=1373 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (low w.registry.nextValue) (low w.asset))
  else original column

theorem seed_value (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column ∈ comparisonValues) : seed original w column = (difference w column : F) := by
  exact if_pos member

theorem seed_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (outside : column ∉ written) : seed original w column = original column := by
  have values : column ∉ comparisonValues := by
    simp only [written,comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at outside ⊢
    tauto
  have flags : column≠981 ∧ column≠1112 ∧ column≠1242 ∧ column≠1373 := by
    simp only [written,List.mem_cons,List.not_mem_nil,or_false] at outside
    tauto
  simp only [seed,if_neg values,if_neg flags.1,if_neg flags.2.1,if_neg flags.2.2.1,if_neg flags.2.2.2]

theorem canonical_values (c : Crypto) (w : TransferSem.Witness) (legal : RegistrySem (crypto c) w) :
    w.asset < 2^255 ∧ w.registry.value < 2^255 ∧ w.registry.nextValue < 2^255 := by
  rcases legal with ⟨_,_,_,_,_,_,value,asset,next,_,_⟩
  exact ⟨lt_trans asset WordNaturalSeed297.field_below_255,
    lt_trans value WordNaturalSeed297.field_below_255,lt_trans next WordNaturalSeed297.field_below_255⟩

theorem high_bound (n : Nat) (bound : n < 2^255) : high n < 2^127 :=
  HighBitMeaning122.high_bound n bound

theorem low_bound (n : Nat) : low n < 2^128 := Nat.mod_lt n (by decide)

theorem difference_bounds (c : Crypto) (w : TransferSem.Witness) (legal : RegistrySem (crypto c) w) :
    difference w 982 < 2^127 ∧ difference w 1113 < 2^128 ∧
    difference w 1243 < 2^127 ∧ difference w 1374 < 2^128 := by
  have canon := canonical_values c w legal
  exact ⟨BoundedLimbComparison119.difference_bound 127 _ _ (high_bound _ canon.1) (high_bound _ canon.2.1),
    BoundedLimbComparison119.difference_bound 128 _ _ (low_bound _) (low_bound _),
    BoundedLimbComparison119.difference_bound 127 _ _ (high_bound _ canon.2.2) (high_bound _ canon.1),
    BoundedLimbComparison119.difference_bound 128 _ _ (low_bound _) (low_bound _)⟩

theorem low_below_field : 2^128 < TransferCore.fieldModulus := by decide +kernel
theorem high_below_field : 2^127 < TransferCore.fieldModulus := by decide +kernel

theorem combined_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (column : Nat) (member : column ∈ comparisonValues) :
    HeaderRegistrySeed299.combined (seed original w) c w column = (difference w column : F) := by
  have bounds : 10 < column ∧ (column < 136 ∨ 184 ≤ column) ∧ column ≠ 22737 := by
    simp only [comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  exact (RegistryNaturalSeed298.untouched _ w.registry column (by
    simp only [comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide) (by rcases bounds.2.1 with before | after <;> omega)).trans
    ((HeaderRegistrySeed299.seed_outside (seed original w) c w column bounds.1 bounds.2.2).trans
      (seed_value original w column member))

theorem comparison_widths_checked : CapturedWordRoot213.words.all (fun entry => decide
    ((entry.1.value=982 → entry.1.width=127) ∧ (entry.1.value=1113 → entry.1.width=128) ∧
     (entry.1.value=1243 → entry.1.width=127) ∧ (entry.1.value=1374 → entry.1.width=128))) = true := by decide +kernel

theorem natural_bounds (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem (crypto c) w) (entry : WordHints210.Slot × Nat)
    (member : entry ∈ CapturedWordRoot213.words) (selected : entry.1.value ∈ comparisonValues) :
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined (seed original w) c w) entry.1.value < 2^entry.1.width := by
  have widths := of_decide_eq_true ((List.all_eq_true.mp comparison_widths_checked) entry member)
  have bounds := difference_bounds c w legal
  change representation.value (HeaderRegistrySeed299.combined (seed original w) c w entry.1.value) < _
  rw [combined_value original c w entry.1.value selected]
  simp only [comparisonValues,List.mem_cons,List.not_mem_nil,or_false] at selected
  rcases selected with first | second | third | fourth
  · rw [first,widths.1 first,RegistryNaturalSeed298.represented_nat _ (lt_trans bounds.1 high_below_field)]
    exact bounds.1
  · rw [second,widths.2.1 second,RegistryNaturalSeed298.represented_nat _ (lt_trans bounds.2.1 low_below_field)]
    exact bounds.2.1
  · rw [third,widths.2.2.1 third,RegistryNaturalSeed298.represented_nat _ (lt_trans bounds.2.2.1 high_below_field)]
    exact bounds.2.2.1
  · rw [fourth,widths.2.2.2 fourth,RegistryNaturalSeed298.represented_nat _ (lt_trans bounds.2.2.2 low_below_field)]
    exact bounds.2.2.2
end ShielddSecurity.RegistryComparisonSeed318

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.comparisonValues
#print axioms ShielddSecurity.RegistryComparisonSeed318.comparisonValues

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.written
#print axioms ShielddSecurity.RegistryComparisonSeed318.written

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.high
#print axioms ShielddSecurity.RegistryComparisonSeed318.high

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.low
#print axioms ShielddSecurity.RegistryComparisonSeed318.low

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.difference
#print axioms ShielddSecurity.RegistryComparisonSeed318.difference

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.seed
#print axioms ShielddSecurity.RegistryComparisonSeed318.seed

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.seed_value
#print axioms ShielddSecurity.RegistryComparisonSeed318.seed_value

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.seed_outside
#print axioms ShielddSecurity.RegistryComparisonSeed318.seed_outside

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.canonical_values
#print axioms ShielddSecurity.RegistryComparisonSeed318.canonical_values

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.high_bound
#print axioms ShielddSecurity.RegistryComparisonSeed318.high_bound

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.low_bound
#print axioms ShielddSecurity.RegistryComparisonSeed318.low_bound

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.difference_bounds
#print axioms ShielddSecurity.RegistryComparisonSeed318.difference_bounds

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.low_below_field
#print axioms ShielddSecurity.RegistryComparisonSeed318.low_below_field

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.high_below_field
#print axioms ShielddSecurity.RegistryComparisonSeed318.high_below_field

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.combined_value
#print axioms ShielddSecurity.RegistryComparisonSeed318.combined_value

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.comparison_widths_checked
#print axioms ShielddSecurity.RegistryComparisonSeed318.comparison_widths_checked

set_option pp.all true in
#check @ShielddSecurity.RegistryComparisonSeed318.natural_bounds
#print axioms ShielddSecurity.RegistryComparisonSeed318.natural_bounds
