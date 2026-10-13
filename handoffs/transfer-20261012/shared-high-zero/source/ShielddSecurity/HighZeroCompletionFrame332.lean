import ShielddSecurity.HighZeroSeed329
import ShielddSecurity.HighZeroHintFrame330
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroCompletionFrame332
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) : Nat → F :=
  SharedComparisonBlocks327.assignment (HighZeroSeed329.seed original w) c w initial

theorem prepared_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (column : Nat) (selected : column ∈ HighZeroHintFrame330.columns) :
    prepared (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w column = HighZeroSeed329.seed original w column := by
  have ranges : 184 ≤ column ∧ column < 22737 := by
    simp only [HighZeroHintFrame330.columns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> omega
  have fixed : column ∉ RegistryNaturalSeed298.fixedColumns := by
    simp only [RegistryNaturalSeed298.fixedColumns,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have unwritten : column ∉ RegistryComparisonSeed318.written := by
    simp only [HighZeroHintFrame330.columns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> simp only [RegistryComparisonSeed318.written,List.mem_cons,List.not_mem_nil,or_false] <;> omega
  exact (prepared_outside _ c w column (by omega) (by constructor <;> norm_num [copy] <;> omega)).trans
    ((RegistryNaturalSeed298.untouched _ w.registry column fixed (by omega)).trans
      ((HeaderRegistrySeed299.seed_outside _ c w column (by omega) (by omega)).trans
        (RegistryComparisonSeed318.seed_outside (HighZeroSeed329.seed original w) w column unwritten)))

theorem group_outside (column : Nat) (selected : column ∈ HighZeroHintFrame330.columns) :
    column ∉ CapturedFourSubgroupSeed89.hintColumns := by
  have lower : 1110 ≤ column := by
    simp only [HighZeroHintFrame330.columns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> omega
  simp only [CapturedFourSubgroupSeed89.hintColumns,List.mem_cons,List.not_mem_nil,or_false]
  omega

theorem indicator_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (column : Nat) (indicator : column=1110 ∨ column=1371) :
    assignment original c w initial column=HighZeroSeed329.seed original w column := by
  have selected : column ∈ HighZeroHintFrame330.columns := by rcases indicator with rfl | rfl <;> decide
  have group := CapturedFourSubgroupSeed89.seeded_outside
    (prepared (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) initial column (group_outside column selected)
  have preparedValue := prepared_frame original c w column selected
  have boolean : HighZeroSeed329.seed original w column=0 ∨ HighZeroSeed329.seed original w column=1 := by
    rcases indicator with rfl | rfl
    · rw [HighZeroSeed329.first_flag]
      exact boolean_sound _ (FieldZeroSeed125.boolean _)
    · rw [HighZeroSeed329.second_flag]
      exact boolean_sound _ (FieldZeroSeed125.boolean _)
  have aliasOutside : ¬Alias column := by
    rcases indicator with first | second <;> simp only [Alias] <;> omega
  have frame := HighZeroHintFrame330.flag_frame
    (CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) initial)
    (normalized (numbers (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w))
    (fallback (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) column selected
    (by rw [group,preparedValue]; exact boolean)
    (by unfold fallback
        rw [LegalAliasMeanings276.fallback_fixed _ _ column aliasOutside]
        unfold ZeroHintWordFrame303.flags
        rw [group])
  exact frame.trans (group.trans preparedValue)

theorem inverse_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (column : Nat) (inverse : column=1111 ∨ column=1372) :
    assignment original c w initial column=HighZeroSeed329.seed original w column := by
  have selected : column ∈ HighZeroHintFrame330.columns := by rcases inverse with rfl | rfl <;> decide
  have bounds : 3 ≤ column ∧ column < 22738 := by rcases inverse with first | second <;> omega
  let base := CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) initial
  let seeded := SharedWordWitness221.seeded base (normalized (numbers (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w))
    (fallback (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w)
  change CapturedFullRelation58.candidate seeded column=HighZeroSeed329.seed original w column
  exact (SharedRegisteredGeneral308.candidate_original seeded column bounds.1 bounds.2).trans
    ((BooleanHints207.seeded_outside base _ _ column (HighZeroHintFrame330.inverse_unselected column inverse)).trans
      ((CapturedFourSubgroupSeed89.seeded_outside _ initial column (group_outside column selected)).trans
        (prepared_frame original c w column selected)))

theorem first_flag (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    assignment original c w initial 1110=FieldZeroSeed125.flag (HighZeroSeed329.firstDelta w) :=
  (indicator_frame original c w initial 1110 (Or.inl rfl)).trans (HighZeroSeed329.first_flag original w)
theorem first_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    assignment original c w initial 1111=(HighZeroSeed329.firstDelta w)⁻¹ :=
  (inverse_frame original c w initial 1111 (Or.inl rfl)).trans (HighZeroSeed329.first_inverse original w)
theorem second_flag (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    assignment original c w initial 1371=FieldZeroSeed125.flag (HighZeroSeed329.secondDelta w) :=
  (indicator_frame original c w initial 1371 (Or.inr rfl)).trans (HighZeroSeed329.second_flag original w)
theorem second_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    assignment original c w initial 1372=(HighZeroSeed329.secondDelta w)⁻¹ :=
  (inverse_frame original c w initial 1372 (Or.inr rfl)).trans (HighZeroSeed329.second_inverse original w)
end ShielddSecurity.HighZeroCompletionFrame332

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.assignment
#print axioms ShielddSecurity.HighZeroCompletionFrame332.assignment

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.prepared_frame
#print axioms ShielddSecurity.HighZeroCompletionFrame332.prepared_frame

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.group_outside
#print axioms ShielddSecurity.HighZeroCompletionFrame332.group_outside

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.indicator_frame
#print axioms ShielddSecurity.HighZeroCompletionFrame332.indicator_frame

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.inverse_frame
#print axioms ShielddSecurity.HighZeroCompletionFrame332.inverse_frame

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.first_flag
#print axioms ShielddSecurity.HighZeroCompletionFrame332.first_flag

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.first_inverse
#print axioms ShielddSecurity.HighZeroCompletionFrame332.first_inverse

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.second_flag
#print axioms ShielddSecurity.HighZeroCompletionFrame332.second_flag

set_option pp.all true in
#check @ShielddSecurity.HighZeroCompletionFrame332.second_inverse
#print axioms ShielddSecurity.HighZeroCompletionFrame332.second_inverse
