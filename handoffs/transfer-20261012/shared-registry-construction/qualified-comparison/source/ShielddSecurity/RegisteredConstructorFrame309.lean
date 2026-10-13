import ShielddSecurity.HeaderSharedConstruction300
import ShielddSecurity.HeaderRegisteredLegality307
import ShielddSecurity.SharedRegisteredGeneral308
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegisteredConstructorFrame309
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272
variable {K : Type} [Field K]

theorem group_term (base : Nat → K) (initial : Fin 4 → Group.Point K)
    (index : Nat) (bound : index < 10) :
    eval (CapturedFourSubgroupSeed89.seeded base initial) (CapturedRegisteredAudit70.zeroTerms index) =
      eval base (CapturedRegisteredAudit70.zeroTerms index) := by
  apply CapturedRegisteredHints72.eval_frame
  intro column coefficient member
  rcases SharedZeroPrimitives305.support index bound column coefficient member with rfl | rfl | rfl | rfl | rfl
  all_goals exact CapturedFourSubgroupSeed89.seeded_outside base initial _ (by decide)

theorem commute (base : Nat → K) (initial : Fin 4 → Group.Point K) :
    CapturedRegisteredHints72.seeded (CapturedFourSubgroupSeed89.seeded base initial) =
      CapturedFourSubgroupSeed89.seeded (CapturedRegisteredHints72.seeded base) initial := by
  funext column
  by_cases inside : 115 ≤ column ∧ column < 135
  · have outside : column ∉ CapturedFourSubgroupSeed89.hintColumns := by
      simp only [CapturedFourSubgroupSeed89.hintColumns,List.mem_cons,List.not_mem_nil,or_false]
      omega
    rw [CapturedFourSubgroupSeed89.seeded_outside _ initial column outside]
    unfold CapturedRegisteredHints72.seeded
    rw [if_pos inside,if_pos inside]
    split_ifs with odd
    · rw [group_term base initial ((column-115)/2) (by omega)]
    · rw [group_term base initial ((column-116)/2) (by omega)]
  · rw [CapturedRegisteredHints72.seeded_outside _ column inside]
    unfold CapturedFourSubgroupSeed89.seeded
    rw [CapturedRegisteredHints72.seeded_outside base column inside]

theorem group_guards (base : Nat → K) (initial : Fin 4 → Group.Point K)
    (legal : CapturedRegisteredHints72.LegalGuards base) :
    CapturedRegisteredHints72.LegalGuards (CapturedFourSubgroupSeed89.seeded base initial) := by
  intro pair bound zero
  rw [group_term base initial (2*pair) (by omega),
    group_term base initial (2*pair+1) (by omega)] at zero
  exact (CapturedFourSubgroupSeed89.seeded_outside base initial 10 (by decide)).trans (legal pair bound zero)

end ShielddSecurity.RegisteredConstructorFrame309
namespace ShielddSecurity.RegisteredConstructorFrame309
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272

def prepared (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) : Nat → F :=
  CapturedRegisteredHints72.seeded (HeaderRegisteredLegality307.base original c w)

theorem prepared_outside (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (column : Nat) (outside : column < 49 ∨ 135 ≤ column)
    (links : column ≠ CompilerArithmeticTransport41.copy ∧ column ≠ 1 ∧ column ≠ 2) :
    prepared original c w column = HeaderRegistrySeed299.combined original c w column := by
  exact (CapturedRegisteredHints72.seeded_outside _ column (by omega)).trans
    ((CapturedEpochHints62.seeded_outside _ _ column (by omega)).trans
      (CompilerVerifierLinks53.seeded_outside _ column links))

theorem word_links_checked : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.value ≠ CompilerArithmeticTransport41.copy ∧ entry.1.value ≠ 1 ∧ entry.1.value ≠ 2)) = true := by decide +kernel

theorem word_values_checked : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.value < 49 ∨ 135 ≤ entry.1.value)) = true := by decide +kernel

theorem word_value (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) :
    prepared original c w entry.1.value = HeaderRegistrySeed299.combined original c w entry.1.value := by
  apply prepared_outside
  · exact of_decide_eq_true ((List.all_eq_true.mp word_values_checked) entry member)
  · have low := of_decide_eq_true ((List.all_eq_true.mp word_links_checked) entry member)
    exact low

theorem registry_frame (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    RegistryRecovery194.recover representation (prepared original c w) =
      RegistryRecovery194.recover representation (HeaderRegistrySeed299.combined original c w) := by
  unfold RegistryRecovery194.recover
  simp only [prepared_outside original c w 11 (by decide) (by constructor <;> decide),
    prepared_outside original c w 12 (by decide) (by constructor <;> decide),
    prepared_outside original c w 13 (by decide) (by constructor <;> decide),
    prepared_outside original c w 14 (by decide) (by constructor <;> decide),
    prepared_outside original c w 15 (by decide) (by constructor <;> decide),
    prepared_outside original c w 21 (by decide) (by constructor <;> decide),
    prepared_outside original c w 22 (by decide) (by constructor <;> decide),
    prepared_outside original c w 23 (by decide) (by constructor <;> decide),
    prepared_outside original c w 24 (by decide) (by constructor <;> decide),
    prepared_outside original c w 30 (by decide) (by constructor <;> decide),
    prepared_outside original c w 31 (by decide) (by constructor <;> decide),
    prepared_outside original c w 32 (by decide) (by constructor <;> decide),
    prepared_outside original c w 33 (by decide) (by constructor <;> decide),
    prepared_outside original c w 34 (by decide) (by constructor <;> decide),
    prepared_outside original c w 35 (by decide) (by constructor <;> decide),
    prepared_outside original c w 36 (by decide) (by constructor <;> decide),
    prepared_outside original c w 42 (by decide) (by constructor <;> decide),
    prepared_outside original c w 43 (by decide) (by constructor <;> decide),
    prepared_outside original c w 135 (by decide) (by constructor <;> decide)]
  congr 1
  funext level slot
  have a := level.isLt
  have b := slot.isLt
  exact congrArg representation.value (prepared_outside original c w (136+3*level.val+slot.val)
    (by omega) (by constructor <;> norm_num [CompilerArithmeticTransport41.copy] <;> omega))

theorem prepared_zero (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    prepared original c w 0 = 1 :=
  (CapturedRegisteredHints72.seeded_outside _ 0 (by decide)).trans
    (HeaderRegisteredLegality307.base_zero original c w)

theorem fallback_agrees (base : Nat → F) (initial : Fin 4 → Group.Point F) (numbers : Nat → Nat) :
    SharedRegisteredGeneral308.Matches (CapturedFourSubgroupSeed89.seeded base initial)
      (LegalAliasMeanings276.fallback numbers (ZeroHintWordFrame303.flags (CapturedRegisteredHints72.seeded base))) := by
  intro column selected
  rw [LegalAliasMeanings276.fallback_fixed numbers _ column (by
    rcases selected with ten | hint
    · subst column; simp only [Alias]; omega
    · simp only [Alias]; omega)]
  unfold SharedRegisteredGeneral308.prepared
  rw [commute base initial]
  have outside : column ∉ CapturedFourSubgroupSeed89.hintColumns := by
    simp only [CapturedFourSubgroupSeed89.hintColumns,List.mem_cons,List.not_mem_nil,or_false]
    rcases selected with ten | hint <;> omega
  unfold ZeroHintWordFrame303.flags
  rw [CapturedFourSubgroupSeed89.seeded_outside _ initial column outside]
end ShielddSecurity.RegisteredConstructorFrame309

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.group_term
#print axioms ShielddSecurity.RegisteredConstructorFrame309.group_term

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.commute
#print axioms ShielddSecurity.RegisteredConstructorFrame309.commute

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.group_guards
#print axioms ShielddSecurity.RegisteredConstructorFrame309.group_guards

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.prepared
#print axioms ShielddSecurity.RegisteredConstructorFrame309.prepared

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.prepared_outside
#print axioms ShielddSecurity.RegisteredConstructorFrame309.prepared_outside

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.word_links_checked
#print axioms ShielddSecurity.RegisteredConstructorFrame309.word_links_checked

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.word_values_checked
#print axioms ShielddSecurity.RegisteredConstructorFrame309.word_values_checked

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.word_value
#print axioms ShielddSecurity.RegisteredConstructorFrame309.word_value

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.registry_frame
#print axioms ShielddSecurity.RegisteredConstructorFrame309.registry_frame

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.prepared_zero
#print axioms ShielddSecurity.RegisteredConstructorFrame309.prepared_zero

set_option pp.all true in
#check @ShielddSecurity.RegisteredConstructorFrame309.fallback_agrees
#print axioms ShielddSecurity.RegisteredConstructorFrame309.fallback_agrees
