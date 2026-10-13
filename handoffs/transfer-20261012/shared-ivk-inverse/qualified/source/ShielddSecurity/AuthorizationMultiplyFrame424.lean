import ShielddSecurity.AuthorizationSharedConstruction422
import ShielddSecurity.AuthorizationMultiplyAvoid423
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationMultiplyFrame424
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def Inside (column : Nat) : Prop := 2252≤column ∧ column≤3765

theorem limits (column : Nat) (inside : Inside column) : 1817<column ∧ column<22737 := by
  change 2252≤column ∧ column≤3765 at inside
  omega

theorem boolean_unselected (column : Nat) (inside : Inside column) : column∉CapturedBooleanRoot209.columns := by
  intro present
  obtain ⟨slot,member,equal⟩ := List.mem_map.mp present
  have excluded := of_decide_eq_true (List.all_eq_true.mp AuthorizationMultiplyAvoid423.checked slot member)
  change slot.2=column at equal
  rw [equal] at excluded
  change column<2252 ∨ 3765<column at excluded
  change 2252≤column ∧ column≤3765 at inside
  omega

theorem word_windows_checked : CapturedWordRoot213.words.all (fun entry =>
    decide (3765<entry.1.start ∨ entry.1.start+entry.1.width≤2252)) = true := by decide +kernel

theorem word_unselected (column : Nat) (inside : Inside column) :
    column∉SharedWordWitness221.wordSlots.flatMap WordHints210.columns := by
  intro present
  obtain ⟨slot,member,inWindow⟩ := List.mem_flatMap.mp present
  obtain ⟨entry,known,equal⟩ := List.mem_map.mp member
  subst slot
  have outside := of_decide_eq_true (List.all_eq_true.mp word_windows_checked entry known)
  change 2252≤column ∧ column≤3765 at inside
  obtain ⟨offset,bound,atColumn⟩ := List.mem_range'.mp inWindow
  simp only [Nat.one_mul] at atColumn
  omega

theorem seed_unselected (column : Nat) (inside : Inside column) : column∉SharedWordWitness221.seedColumns := by
  intro member
  rcases List.mem_append.mp member with boolean|word
  · exact boolean_unselected column inside boolean
  · exact word_unselected column inside word

theorem completed_outside (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (column : Nat) (inside : Inside column) : SharedWordWitness221.completed base numbers fallback column=base column := by
  have limits : 3≤column ∧ column<22738 := by have := limits column inside; omega
  unfold SharedWordWitness221.completed
  exact (SharedRegisteredGeneral308.candidate_original _ column limits.1 limits.2).trans
    (BooleanHints207.seeded_outside base _ _ column (seed_unselected column inside))

theorem original_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (inside : Inside column) :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial column=original column := by
  have limits := limits column inside
  have user : column∉UserWordSeed342.values := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false]
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
    (by omega) (by omega)

theorem seeded_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (inside : Inside column) :
    UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w column=original column := by
  have bounds : 2252≤column ∧ column≤3765 := inside
  rw [UserPathSeed361.outside _ w column (by omega) (by omega) (by omega) (by omega),
    AuthScalarSeed366.seed_outside _ w column (by
      simp only [AuthScalarSeed366.values,List.mem_cons,List.not_mem_nil,or_false];omega),
    RemainingWordSeed369.seed_outside original w column (by
      intro member
      have checked : RemainingWordSeed369.values.all (fun column => decide (3766<column)) = true := by decide +kernel
      have lower := of_decide_eq_true (List.all_eq_true.mp checked column member)
      omega)]

theorem completed_hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : Inside column) :
    AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial column=original column := by
  have bounds : 2252≤column ∧ column≤3765 := inside
  unfold AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment
  rw [original_frame _ c w initial senderInitial receiverInitial column inside,
    seeded_outside _ w column inside,
    AuthorizationPointSeed405.outside _ w authInitial column (by omega) (by omega)]
  exact AuthorizationSharedSeed416.outside original c w column (by omega)

end ShielddSecurity.AuthorizationMultiplyFrame424

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.Inside
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.Inside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.limits
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.limits

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.boolean_unselected
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.boolean_unselected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.word_windows_checked
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.word_windows_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.word_unselected
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.word_unselected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.seed_unselected
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.seed_unselected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.completed_outside
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.completed_outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.original_frame
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.original_frame

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.seeded_outside
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.seeded_outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyFrame424.completed_hint
#print axioms ShielddSecurity.AuthorizationMultiplyFrame424.completed_hint
