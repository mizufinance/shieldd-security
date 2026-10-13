import ShielddSecurity.UserPathSeed361
import ShielddSecurity.UserRecordAvoid362
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathFrame363
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def Inside (column : Nat) : Prop :=
  column=1528 ∨ column=1766 ∨ (1531≤column ∧ column<1579) ∨ (1769≤column ∧ column<1817)

theorem boolean_unselected (column : Nat) (inside : Inside column) : column∉CapturedBooleanRoot209.columns := by
  intro present
  obtain ⟨slot,member,equal⟩ := List.mem_map.mp present
  have excluded := of_decide_eq_true (List.all_eq_true.mp UserRecordAvoid362.checked slot member)
  change slot.2=column at equal
  rw [equal] at excluded
  have range : (1504≤column ∧ column<1579) ∨ (1742≤column ∧ column<1817) := by unfold Inside at inside; omega
  exact Or.elim range excluded.1 excluded.2

theorem word_windows_checked : CapturedWordRoot213.words.all (fun entry => decide
    ((entry.1.start+entry.1.width≤1504 ∨ 1579≤entry.1.start) ∧
     (entry.1.start+entry.1.width≤1742 ∨ 1817≤entry.1.start))) = true := by decide +kernel

theorem word_unselected (column : Nat) (inside : Inside column) :
    column∉SharedWordWitness221.wordSlots.flatMap WordHints210.columns := by
  intro present
  obtain ⟨slot,member,inWindow⟩ := List.mem_flatMap.mp present
  obtain ⟨entry,known,equal⟩ := List.mem_map.mp member
  subst slot
  have outside := of_decide_eq_true (List.all_eq_true.mp word_windows_checked entry known)
  obtain ⟨offset,bound,atColumn⟩ := List.mem_range'.mp inWindow
  simp only [Nat.one_mul] at atColumn
  unfold Inside at inside
  omega

theorem seed_unselected (column : Nat) (inside : Inside column) : column∉SharedWordWitness221.seedColumns := by
  intro member
  rcases List.mem_append.mp member with boolean|word
  · exact boolean_unselected column inside boolean
  · exact word_unselected column inside word

theorem completed_outside (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (column : Nat) (inside : Inside column) : SharedWordWitness221.completed base numbers fallback column=base column := by
  have limits : 3≤column ∧ column<22738 := by unfold Inside at inside; omega
  unfold SharedWordWitness221.completed
  exact (SharedRegisteredGeneral308.candidate_original _ column limits.1 limits.2).trans
    (BooleanHints207.seeded_outside base _ _ column (seed_unselected column inside))

theorem original_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (inside : Inside column) :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial column=original column := by
  have limits : 1374<column ∧ column<1817 := by unfold Inside at inside; omega
  have user : column∉UserWordSeed342.values := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false]
    unfold Inside at inside
    omega
  unfold UserLifecycleWord345.assignment HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment HeaderRegisteredConstruction310.completed
  apply Eq.trans (completed_outside _ _ _ column inside)
  apply Eq.trans (CapturedFourSubgroupSeed89.seeded_outside _ initial column (by
    simp only [CapturedFourSubgroupSeed89.hintColumns,List.mem_cons,List.not_mem_nil,or_false]
    omega))
  rw [RegisteredConstructorFrame309.prepared_outside _ c w column (Or.inr (by omega))
    (by change column≠200692 ∧ column≠1 ∧ column≠2; omega)]
  unfold HeaderRegistrySeed299.combined
  rw [RegistryNaturalSeed298.untouched _ w.registry column (by
    simp only [RegistryNaturalSeed298.fixedColumns,List.mem_cons,List.not_mem_nil,or_false]; omega) (by omega),
    HeaderRegistrySeed299.seed_outside _ c w column (by omega) (by omega),
    RegistryComparisonSeed318.seed_outside _ w column (by
      simp only [RegistryComparisonSeed318.written,List.mem_cons,List.not_mem_nil,or_false]; omega),
    HighZeroSeed329.outside _ w column (Or.inr (by omega)) (Or.inr (by omega)),UserWordSeed342.seed_outside _ w column user]
  exact UserSubgroupSeed352.outside original w senderInitial receiverInitial column
    (by unfold Inside at inside; omega) (by unfold Inside at inside; omega)

theorem commitments (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed original w) w senderInitial receiverInitial) c w initial 1528=(w.sender.rnkCommitment:F) ∧
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed original w) w senderInitial receiverInitial) c w initial 1766=(w.receiver.rnkCommitment:F) :=
  ⟨(original_frame (UserPathSeed361.seed original w) c w initial senderInitial receiverInitial 1528 (Or.inl rfl)).trans (UserPathSeed361.commitments original w).1,
   (original_frame (UserPathSeed361.seed original w) c w initial senderInitial receiverInitial 1766 (Or.inr (Or.inl rfl))).trans (UserPathSeed361.commitments original w).2⟩

theorem sender_siblings (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) (level : Fin 16) (slot : Fin 3) :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed original w) w senderInitial receiverInitial) c w initial
      (1531+3*level.val+slot.val)=(w.sender.siblings level slot:F) := by
  have levelBound := level.isLt
  have slotBound := slot.isLt
  exact (original_frame (UserPathSeed361.seed original w) c w initial senderInitial receiverInitial _ (Or.inr (Or.inr (Or.inl (by constructor <;> omega))))).trans
    (UserPathSeed361.sender_siblings original w level slot)

theorem receiver_siblings (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) (level : Fin 16) (slot : Fin 3) :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed (UserPathSeed361.seed original w) w senderInitial receiverInitial) c w initial
      (1769+3*level.val+slot.val)=(w.receiver.siblings level slot:F) := by
  have levelBound := level.isLt
  have slotBound := slot.isLt
  exact (original_frame (UserPathSeed361.seed original w) c w initial senderInitial receiverInitial _ (Or.inr (Or.inr (Or.inr (by constructor <;> omega))))).trans
    (UserPathSeed361.receiver_siblings original w level slot)

end ShielddSecurity.UserPathFrame363

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.Inside
#print axioms ShielddSecurity.UserPathFrame363.Inside

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.boolean_unselected
#print axioms ShielddSecurity.UserPathFrame363.boolean_unselected

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.word_windows_checked
#print axioms ShielddSecurity.UserPathFrame363.word_windows_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.word_unselected
#print axioms ShielddSecurity.UserPathFrame363.word_unselected

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.seed_unselected
#print axioms ShielddSecurity.UserPathFrame363.seed_unselected

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.completed_outside
#print axioms ShielddSecurity.UserPathFrame363.completed_outside

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.original_frame
#print axioms ShielddSecurity.UserPathFrame363.original_frame

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.commitments
#print axioms ShielddSecurity.UserPathFrame363.commitments

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.sender_siblings
#print axioms ShielddSecurity.UserPathFrame363.sender_siblings

set_option pp.all true in
#check @ShielddSecurity.UserPathFrame363.receiver_siblings
#print axioms ShielddSecurity.UserPathFrame363.receiver_siblings
