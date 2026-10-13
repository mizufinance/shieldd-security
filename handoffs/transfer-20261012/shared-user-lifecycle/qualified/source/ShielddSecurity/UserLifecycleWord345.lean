import ShielddSecurity.UserWordConstruction343
import ShielddSecurity.UserLifecycleBits344
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserLifecycleWord345
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def originalBase (original : Nat → F) (w : TransferSem.Witness) : Nat → F :=
  RegistryComparisonSeed318.seed (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) w

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) : Nat → F :=
  HighZeroCompletionFrame332.assignment (UserWordSeed342.seed original w) c w initial

theorem prepared_number (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (column : Nat) (user : column ∈ UserWordSeed342.values) :
    HeaderRegisteredConstruction310.numbers (originalBase original w) c w column = UserWordSeed342.value w column := by
  have limits : 135 ≤ column ∧ column < 2000 := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false] at user
    rcases user with rfl|rfl|rfl|rfl <;> constructor <;> decide
  change representation.value (RegisteredConstructorFrame309.prepared (originalBase original w) c w column) = _
  rw [RegisteredConstructorFrame309.prepared_outside _ c w column (Or.inr limits.1) (by change column≠200692 ∧ column≠1 ∧ column≠2; omega)]
  have same := UserWordSeed342.combined_value original c w column user
  change HeaderRegistrySeed299.combined (originalBase original w) c w column = _ at same
  rw [same,RegistryNaturalSeed298.represented_nat _
    (lt_trans (UserWordSeed342.value_bound c w legal column user) (UserWordSeed342.width_below_field column))]

theorem selected_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w)
    (entry : WordHints210.Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (user : entry.1.value ∈ UserWordSeed342.values) :
    ∀ index < entry.1.width, assignment original c w initial (entry.1.start+index) =
      BooleanHints207.bitValue ((encodeBits entry.1.width (UserWordSeed342.value w entry.1.value))[index]?.getD false) := by
  intro index bound
  have point := SharedWordLimbMeaning321.encoded_point
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared (originalBase original w) c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers (originalBase original w) c w))
    (HeaderRegisteredConstruction310.fallback (originalBase original w) c w)
    (LegalWordNormalization272.coherent _) entry member index bound
  have outside : ¬ LegalWordNormalization272.Alias entry.1.value := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false] at user
    rcases user with h|h|h|h <;> rw [h] <;> decide
  have fixed := (LegalWordNormalization272.fixed
    (HeaderRegisteredConstruction310.numbers (originalBase original w) c w) entry.1.value outside).trans
    (prepared_number original c w legal entry.1.value user)
  change assignment original c w initial (entry.1.start+index) = _ at point
  rw [fixed] at point
  exact point

theorem sender_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index < 131, assignment original c w initial (1611+index) =
      BooleanHints207.bitValue ((encodeBits 131 (w.sender.lifecycle))[index]?.getD false) :=
  selected_bits original c w initial legal
    (CapturedWordSlots211B003.W12.slot,CapturedWordSlots211B003.W12.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))) (by decide)

theorem receiver_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index < 131, assignment original c w initial (1849+index) =
      BooleanHints207.bitValue ((encodeBits 131 (w.receiver.lifecycle))[index]?.getD false) :=
  selected_bits original c w initial legal
    (CapturedWordSlots211B003.W15.slot,CapturedWordSlots211B003.W15.first) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))) (by decide)

theorem control (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : assignment original c w initial 10=(if w.regulated then 1 else 0) := by
  exact SharedRegulatedValue316.control_meaning (originalBase original w) c w initial

def bitIndex (index : Nat) : Nat := if index<3 then index else index+64

theorem gated_bit (regulated : Bool) (lifecycle index : Nat) (inside : index<67)
    (active : regulated=true → lifecycle%8=1 ∧ lifecycle/2^67=0) :
    (if regulated then (1:F) else 0)*
      (BooleanHints207.bitValue ((encodeBits 131 lifecycle)[bitIndex index]?.getD false)-
        (if index=0 then 1 else 0))=0 := by
  cases flag : regulated
  · simp only [Bool.false_eq_true,if_false,zero_mul]
  · have meaning := active flag
    by_cases low : index<3
    · rw [bitIndex,if_pos low,UserLifecycleBits344.status_bit lifecycle index meaning.1 low]
      by_cases zero : index=0 <;> simp [BooleanHints207.bitValue,zero]
    · have nonzero : index≠0 := by omega
      rw [bitIndex,if_neg low,UserLifecycleBits344.high_bit lifecycle (index+64) meaning.2 (by omega) (by omega)]
      simp only [BooleanHints207.bitValue,Bool.false_eq_true,if_false,if_neg nonzero,sub_self,mul_zero]
end ShielddSecurity.UserLifecycleWord345

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.originalBase
#print axioms ShielddSecurity.UserLifecycleWord345.originalBase

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.assignment
#print axioms ShielddSecurity.UserLifecycleWord345.assignment

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.prepared_number
#print axioms ShielddSecurity.UserLifecycleWord345.prepared_number

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.selected_bits
#print axioms ShielddSecurity.UserLifecycleWord345.selected_bits

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.sender_bits
#print axioms ShielddSecurity.UserLifecycleWord345.sender_bits

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.receiver_bits
#print axioms ShielddSecurity.UserLifecycleWord345.receiver_bits

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.control
#print axioms ShielddSecurity.UserLifecycleWord345.control

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.bitIndex
#print axioms ShielddSecurity.UserLifecycleWord345.bitIndex

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleWord345.gated_bit
#print axioms ShielddSecurity.UserLifecycleWord345.gated_bit
