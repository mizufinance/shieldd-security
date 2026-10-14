import ShielddSecurity.AuthorizationSharedConstruction422
import ShielddSecurity.PublishedPointAvoid582
import ShielddSecurity.PayloadBindings565
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedPointFrame583
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

abbrev Inside := PublishedPointLayout581.Inside

theorem limits (column : Nat) (inside : Inside column) : 1817<column ∧ column<22737 := by
  have := PublishedPointLayout581.bounds column inside
  omega

theorem boolean_unselected (column : Nat) (inside : Inside column) : column∉CapturedBooleanRoot209.columns := by
  intro present
  obtain ⟨slot,member,equal⟩ := List.mem_map.mp present
  have excluded := List.all_eq_true.mp PublishedPointAvoid582.checked slot member
  change slot.2=column at equal
  rw [equal] at excluded
  exact PublishedPointLayout581.excluded column excluded inside

theorem word_windows_checked : CapturedWordRoot213.words.all (fun entry =>
    PublishedPointLayout581.starts.all (fun start =>
      decide (start+2≤entry.1.start ∨ entry.1.start+entry.1.width≤start))) = true := by decide +kernel

theorem word_unselected (column : Nat) (inside : Inside column) :
    column∉SharedWordWitness221.wordSlots.flatMap WordHints210.columns := by
  intro present
  obtain ⟨slot,member,inWindow⟩ := List.mem_flatMap.mp present
  obtain ⟨entry,known,equal⟩ := List.mem_map.mp member
  subst slot
  obtain ⟨start,inStarts,lower,upper⟩ := inside
  have outside := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp word_windows_checked entry known) start inStarts)
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
  have bounds := PublishedPointLayout581.bounds column inside
  rw [UserPathSeed361.outside _ w column (by omega) (by omega) (by omega) (by omega),
    AuthScalarSeed366.seed_outside _ w column (by
      simp only [AuthScalarSeed366.values,List.mem_cons,List.not_mem_nil,or_false];omega),
    RemainingWordSeed369.seed_outside original w column (by
      intro member
      have checked : RemainingWordSeed369.values.all PublishedPointLayout581.outside = true := by decide +kernel
      exact PublishedPointLayout581.excluded column (List.all_eq_true.mp checked column member) inside)]

theorem completed_hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : Inside column) :
    AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := PublishedPointLayout581.bounds column inside
  unfold AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment
  rw [original_frame _ c w initial senderInitial receiverInitial column inside,
    seeded_outside _ w column inside,
    AuthorizationPointSeed405.outside _ w authInitial column (by omega) (by omega)]
  exact AuthorizationSharedSeed416.outside original c w column (by omega)

theorem rk_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : Inside column) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := PublishedPointLayout581.bounds column inside
  let chosen := AuthorizationFixedDomain485.withGenerator c
  let fixed := AuthorizationFixedSeed487.seed (AuthorizationRkSeed505.seed original w rkInitial) w.auth.randomizer
  let dh := AuthorizationDhSeed473.seed fixed chosen w legal
  let traced := AuthorizationTraceSeed451.seed dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk
  have preserved := completed_hint (IvkInverseSeed426.seed traced w)
    (ConcreteAuthorizationCrypto430.withOperations chosen) w authInitial initial senderInitial receiverInitial column inside
  apply preserved.trans
  rw [IvkInverseSeed426.outside traced w column (by omega)]
  dsimp only [traced]
  rw [AuthorizationTraceSeed451.outside dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk column (Or.inr (by omega))]
  have outside : dh column=fixed column := by
    simp only [dh,AuthorizationDhSeed473.seed,if_neg (show column≠3765 by omega)]
  apply outside.trans
  dsimp only [fixed]
  rw [AuthorizationFixedSeed487.outside (AuthorizationRkSeed505.seed original w rkInitial) w.auth.randomizer column (Or.inr (by omega))]
  simp only [AuthorizationRkSeed505.seed,if_neg (show column≠4271 by omega),
    if_neg (show ¬(4272≤column ∧ column<4280) by omega)]

theorem fixed_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (inside : Inside column) : FixedFamilySeed549.seed original w column=original column := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [PublishedPointLayout581.starts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [FixedFamilySeed549.seed,FixedFamilySeed549.one,
      if_neg (show ¬(16406≤column ∧ column<16406+252) by omega),
      if_neg (show ¬(15144≤column ∧ column<15144+252) by omega),
      if_neg (show ¬(13882≤column ∧ column<13882+252) by omega),
      if_neg (show ¬(11864≤column ∧ column<11864+252) by omega),
      if_neg (show ¬(10336≤column ∧ column<10336+252) by omega),
      if_neg (show ¬(8804≤column ∧ column<8804+252) by omega),
      if_neg (show ¬(6587≤column ∧ column<6587+252) by omega),
      if_neg (show ¬(5183≤column ∧ column<5183+252) by omega)]

theorem retained_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : Inside column) :
    FixedFamilyBindings551.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  unfold FixedFamilyBindings551.assignment
  rw [rk_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial column inside]
  exact fixed_seed_outside original w column inside

theorem payload_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (column : Nat) (inside : Inside column) : PayloadTraceSeed564.seed original c w legal column=original column := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [PublishedPointLayout581.starts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [PayloadTraceSeed564.seed,PayloadTraceSeed564.one,
      if_neg (show ¬(5436≤column ∧ column<5436+756) by omega),
      if_neg (show ¬(6840≤column ∧ column<6840+756) by omega)]

theorem payload_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : Inside column) :
    PayloadBindings565.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  unfold PayloadBindings565.assignment
  rw [retained_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial column inside]
  exact payload_seed_outside original c w legal column inside

end ShielddSecurity.PublishedPointFrame583

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.Inside
#print axioms ShielddSecurity.PublishedPointFrame583.Inside

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.limits
#print axioms ShielddSecurity.PublishedPointFrame583.limits

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.boolean_unselected
#print axioms ShielddSecurity.PublishedPointFrame583.boolean_unselected

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.word_windows_checked
#print axioms ShielddSecurity.PublishedPointFrame583.word_windows_checked

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.word_unselected
#print axioms ShielddSecurity.PublishedPointFrame583.word_unselected

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.seed_unselected
#print axioms ShielddSecurity.PublishedPointFrame583.seed_unselected

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.completed_outside
#print axioms ShielddSecurity.PublishedPointFrame583.completed_outside

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.original_frame
#print axioms ShielddSecurity.PublishedPointFrame583.original_frame

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.seeded_outside
#print axioms ShielddSecurity.PublishedPointFrame583.seeded_outside

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.completed_hint
#print axioms ShielddSecurity.PublishedPointFrame583.completed_hint

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.rk_frame
#print axioms ShielddSecurity.PublishedPointFrame583.rk_frame

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.fixed_seed_outside
#print axioms ShielddSecurity.PublishedPointFrame583.fixed_seed_outside

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.retained_frame
#print axioms ShielddSecurity.PublishedPointFrame583.retained_frame

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.payload_seed_outside
#print axioms ShielddSecurity.PublishedPointFrame583.payload_seed_outside

set_option pp.all true in
#check @ShielddSecurity.PublishedPointFrame583.payload_frame
#print axioms ShielddSecurity.PublishedPointFrame583.payload_frame
