import ShielddSecurity.RegistryComparisonConstruction319
import ShielddSecurity.SharedWordLimbMeaning321
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryWordBits322
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

theorem registry_numbers (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    numbers (RegistryComparisonSeed318.seed original w) c w 11 = w.registry.value ∧
    numbers (RegistryComparisonSeed318.seed original w) c w 13 = w.registry.nextValue := by
  have recovered := (registry_frame (RegistryComparisonSeed318.seed original w) c w).trans
    (HeaderRegistrySeed299.recover_registry (RegistryComparisonSeed318.seed original w) c w legal.1)
  exact ⟨congrArg (fun leaf : AssetLeaf => leaf.value) recovered,
    congrArg (fun leaf : AssetLeaf => leaf.nextValue) recovered⟩

theorem asset_number (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    numbers (RegistryComparisonSeed318.seed original w) c w 6 = w.asset := by
  have same := prepared_outside (RegistryComparisonSeed318.seed original w) c w 6 (by decide) (by constructor <;> decide)
  have header := (HeaderRegistrySeed299.original_headers (RegistryComparisonSeed318.seed original w) c w).2.2.2.2.2.2.1
  have bound : w.asset < TransferCore.fieldModulus := by
    rcases legal.2.1.1 with ⟨_,_,_,_,_,_,_,asset,_,_,_⟩
    exact asset
  exact (congrArg representation.value (same.trans header)).trans (RegistryNaturalSeed298.represented_nat _ bound)

theorem value_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index < 255, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial
      (CapturedWordSlots211B000.W03.slot.start+index) =
      if (encodeBits 255 (w.registry.value))[index]?.getD false then 1 else 0 := by
  have fields := SharedWordLimbMeaning321.full_field_bits
    (CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed original w) c w) initial)
    (normalized (numbers (RegistryComparisonSeed318.seed original w) c w))
    (fallback (RegistryComparisonSeed318.seed original w) c w)
    (LegalWordNormalization272.coherent _)
    (CapturedWordSlots211B000.W03.slot,CapturedWordSlots211B000.W03.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) (by rfl)
  have fixed : normalized (numbers (RegistryComparisonSeed318.seed original w) c w) 11 = w.registry.value :=
    (LegalWordNormalization272.fixed _ 11 (by decide)).trans ((registry_numbers original c w legal).1)
  change (∀ index < 255, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial
    (CapturedWordSlots211B000.W03.slot.start+index) =
    if (encodeBits 255 (normalized (numbers (RegistryComparisonSeed318.seed original w) c w) 11))[index]?.getD false then 1 else 0) at fields
  simpa only [fixed] using fields

theorem asset_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index < 255, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial
      (CapturedWordSlots211B001.W04.slot.start+index) =
      if (encodeBits 255 (w.asset))[index]?.getD false then 1 else 0 := by
  have fields := SharedWordLimbMeaning321.full_field_bits
    (CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed original w) c w) initial)
    (normalized (numbers (RegistryComparisonSeed318.seed original w) c w))
    (fallback (RegistryComparisonSeed318.seed original w) c w)
    (LegalWordNormalization272.coherent _)
    (CapturedWordSlots211B001.W04.slot,CapturedWordSlots211B001.W04.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) (by rfl)
  have fixed : normalized (numbers (RegistryComparisonSeed318.seed original w) c w) 6 = w.asset :=
    (LegalWordNormalization272.fixed _ 6 (by decide)).trans (asset_number original c w legal)
  change (∀ index < 255, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial
    (CapturedWordSlots211B001.W04.slot.start+index) =
    if (encodeBits 255 (normalized (numbers (RegistryComparisonSeed318.seed original w) c w) 6))[index]?.getD false then 1 else 0) at fields
  simpa only [fixed] using fields

theorem next_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index < 255, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial
      (CapturedWordSlots211B001.W05.slot.start+index) =
      if (encodeBits 255 (w.registry.nextValue))[index]?.getD false then 1 else 0 := by
  have fields := SharedWordLimbMeaning321.full_field_bits
    (CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed original w) c w) initial)
    (normalized (numbers (RegistryComparisonSeed318.seed original w) c w))
    (fallback (RegistryComparisonSeed318.seed original w) c w)
    (LegalWordNormalization272.coherent _)
    (CapturedWordSlots211B001.W05.slot,CapturedWordSlots211B001.W05.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) (by rfl)
  have fixed : normalized (numbers (RegistryComparisonSeed318.seed original w) c w) 13 = w.registry.nextValue :=
    (LegalWordNormalization272.fixed _ 13 (by decide)).trans ((registry_numbers original c w legal).2)
  change (∀ index < 255, HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial
    (CapturedWordSlots211B001.W05.slot.start+index) =
    if (encodeBits 255 (normalized (numbers (RegistryComparisonSeed318.seed original w) c w) 13))[index]?.getD false then 1 else 0) at fields
  simpa only [fixed] using fields

end ShielddSecurity.RegistryWordBits322

set_option pp.all true in
#check @ShielddSecurity.RegistryWordBits322.registry_numbers
#print axioms ShielddSecurity.RegistryWordBits322.registry_numbers

set_option pp.all true in
#check @ShielddSecurity.RegistryWordBits322.asset_number
#print axioms ShielddSecurity.RegistryWordBits322.asset_number

set_option pp.all true in
#check @ShielddSecurity.RegistryWordBits322.value_bits
#print axioms ShielddSecurity.RegistryWordBits322.value_bits

set_option pp.all true in
#check @ShielddSecurity.RegistryWordBits322.asset_bits
#print axioms ShielddSecurity.RegistryWordBits322.asset_bits

set_option pp.all true in
#check @ShielddSecurity.RegistryWordBits322.next_bits
#print axioms ShielddSecurity.RegistryWordBits322.next_bits
