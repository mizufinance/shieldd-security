import ShielddSecurity.AuthorizationPointSeed405
import ShielddSecurity.AuthorizationPointAvoid406
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPointFrame407
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def values : List Nat := List.range' 1980 8 ++ [1993]
def Inside (column : Nat) : Prop := column∈values

theorem limits_checked : values.all (fun column => decide (1817<column ∧ column<22737)) = true := by decide +kernel

theorem limits (column : Nat) (inside : Inside column) : 1817<column ∧ column<22737 :=
  of_decide_eq_true (List.all_eq_true.mp limits_checked column inside)

theorem boolean_unselected (column : Nat) (inside : Inside column) : column∉CapturedBooleanRoot209.columns := by
  intro present
  obtain ⟨slot,member,equal⟩ := List.mem_map.mp present
  have excluded := of_decide_eq_true (List.all_eq_true.mp AuthorizationPointAvoid406.checked slot member)
  change slot.2=column at equal
  rw [equal] at excluded
  change column∉values at excluded
  exact excluded inside

theorem word_windows_checked : CapturedWordRoot213.words.all (fun entry =>
    values.all (fun column => decide (column<entry.1.start ∨ entry.1.start+entry.1.width≤column))) = true := by decide +kernel

theorem word_unselected (column : Nat) (inside : Inside column) :
    column∉SharedWordWitness221.wordSlots.flatMap WordHints210.columns := by
  intro present
  obtain ⟨slot,member,inWindow⟩ := List.mem_flatMap.mp present
  obtain ⟨entry,known,equal⟩ := List.mem_map.mp member
  subst slot
  have outside := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp word_windows_checked entry known) column inside)
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

theorem point_inside (offset : Fin 8) : Inside (1980+offset.val) := by
  have present : 1980+offset.val∈List.range' 1980 8 := List.mem_range'.mpr ⟨offset.val,offset.isLt,by simp only [Nat.one_mul]⟩
  exact List.mem_append_left _ present

theorem key_inside : Inside 1993 := List.mem_append_right _ (List.mem_cons_self)

theorem seeded_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (inside : Inside column) :
    UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w column=original column := by
  have bounds : 1980≤column ∧ column≤1993 := by
    have checked : values.all (fun column => decide (1980≤column ∧ column≤1993)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
  rw [UserPathSeed361.outside _ w column (by omega) (by omega) (by omega) (by omega),
    AuthScalarSeed366.seed_outside _ w column (by
      simp only [AuthScalarSeed366.values,List.mem_cons,List.not_mem_nil,or_false];omega),
    RemainingWordSeed369.seed_outside original w column (by
      intro member
      have checked : RemainingWordSeed369.values.all (fun column => decide (3766<column)) = true := by decide +kernel
      have lower := of_decide_eq_true (List.all_eq_true.mp checked column member)
      omega)]

theorem completed_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (offset : Fin 8) :
    SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial
      (1980+offset.val)=AuthorizationPointSeed405.value w authInitial offset.val := by
  unfold SemanticWordFrame373.assignment
  rw [original_frame _ c w initial senderInitial receiverInitial _ (point_inside offset),
    seeded_outside _ w _ (point_inside offset),AuthorizationPointSeed405.point_value original w authInitial offset]

theorem completed_key (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial 1993=(w.auth.nk:F) := by
  unfold SemanticWordFrame373.assignment
  rw [original_frame _ c w initial senderInitial receiverInitial 1993 key_inside,
    seeded_outside _ w 1993 key_inside,AuthorizationPointSeed405.key_value original w authInitial]

end ShielddSecurity.AuthorizationPointFrame407

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.values
#print axioms ShielddSecurity.AuthorizationPointFrame407.values

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.Inside
#print axioms ShielddSecurity.AuthorizationPointFrame407.Inside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.limits_checked
#print axioms ShielddSecurity.AuthorizationPointFrame407.limits_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.limits
#print axioms ShielddSecurity.AuthorizationPointFrame407.limits

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.boolean_unselected
#print axioms ShielddSecurity.AuthorizationPointFrame407.boolean_unselected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.word_windows_checked
#print axioms ShielddSecurity.AuthorizationPointFrame407.word_windows_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.word_unselected
#print axioms ShielddSecurity.AuthorizationPointFrame407.word_unselected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.seed_unselected
#print axioms ShielddSecurity.AuthorizationPointFrame407.seed_unselected

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.completed_outside
#print axioms ShielddSecurity.AuthorizationPointFrame407.completed_outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.original_frame
#print axioms ShielddSecurity.AuthorizationPointFrame407.original_frame

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.point_inside
#print axioms ShielddSecurity.AuthorizationPointFrame407.point_inside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.key_inside
#print axioms ShielddSecurity.AuthorizationPointFrame407.key_inside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.seeded_outside
#print axioms ShielddSecurity.AuthorizationPointFrame407.seeded_outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.completed_point
#print axioms ShielddSecurity.AuthorizationPointFrame407.completed_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointFrame407.completed_key
#print axioms ShielddSecurity.AuthorizationPointFrame407.completed_key
