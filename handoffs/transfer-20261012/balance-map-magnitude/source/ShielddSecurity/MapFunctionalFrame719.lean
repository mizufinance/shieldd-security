import ShielddSecurity.BalanceBlindingBindings680
import ShielddSecurity.MapCompletionFlags718
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapFunctionalFrame719
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def Region (column : Nat) : Prop := 20934≤column ∧ column<21199

theorem seeded_outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (inside : Region column) :
    UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  rw [UserPathSeed361.outside _ w column (by omega) (by omega) (by omega) (by omega),
    AuthScalarSeed366.seed_outside _ w column (by
      simp only [AuthScalarSeed366.values,List.mem_cons,List.not_mem_nil,or_false];omega),
    RemainingWordSeed369.seed_outside original w column (by
      simp only [RemainingWordSeed369.values,List.mem_cons,List.not_mem_nil,or_false]
      omega)]

theorem fixed_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (inside : Region column) : FixedFamilySeed549.seed original w column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  simp only [FixedFamilySeed549.seed,FixedFamilySeed549.one,
      if_neg (show ¬(16406≤column ∧ column<16406+252) by omega),
      if_neg (show ¬(15144≤column ∧ column<15144+252) by omega),
      if_neg (show ¬(13882≤column ∧ column<13882+252) by omega),
      if_neg (show ¬(11864≤column ∧ column<11864+252) by omega),
      if_neg (show ¬(10336≤column ∧ column<10336+252) by omega),
      if_neg (show ¬(8804≤column ∧ column<8804+252) by omega),
      if_neg (show ¬(6587≤column ∧ column<6587+252) by omega),
      if_neg (show ¬(5183≤column ∧ column<5183+252) by omega)]

theorem payload_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (column : Nat) (inside : Region column) : PayloadTraceSeed564.seed original c w legal column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  simp only [PayloadTraceSeed564.seed,PayloadTraceSeed564.one,
      if_neg (show ¬(5436≤column ∧ column<5436+756) by omega),
      if_neg (show ¬(6840≤column ∧ column<6840+756) by omega)]

theorem published_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (inside : Region column) : PublishedPointSeed584.seed original w column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  unfold PublishedPointSeed584.seed <;>
  split <;> first | rfl | (exfalso;omega)

theorem inverse_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (inside : Region column) : PublishedInverseSeed592.seed original w column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  unfold PublishedInverseSeed592.seed <;>
  split <;> first | rfl | (exfalso;omega)

theorem ownership_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (column : Nat) (inside : Region column) : OwnershipTrace603.seed original c w legal column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  unfold OwnershipTrace603.seed
  rw [OwnershipTrace603.one_outside _ _ _ 9322 _ (Or.inr (by omega)),
    OwnershipTrace603.one_outside _ _ _ 10854 _ (Or.inr (by omega))]

theorem tier_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (column : Nat) (inside : Region column) : TierTrace616.seed original c w legal column=original column := by
  have bounds : 20934≤column ∧ column<21199 := inside
  unfold TierTrace616.seed
  rw [TierTrace616.one_outside _ _ _ 12117 _ (Or.inr (by omega)),
    TierTrace616.one_outside _ _ _ 12873 _ (Or.inr (by omega)),
    TierTrace616.one_outside _ _ _ 14135 _ (Or.inr (by omega)),
    TierTrace616.one_outside _ _ _ 15397 _ (Or.inr (by omega)),
    TierTrace616.one_outside _ _ _ 16659 _ (Or.inr (by omega))]

theorem prepared_original (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : Region column) :
    RegisteredConstructorFrame309.prepared
      (UserLifecycleWord345.originalBase (UserSubgroupSeed352.seed original w senderInitial receiverInitial) w) c w column=original column := by
  have limits : 20934≤column ∧ column<21199 := inside
  have user : column∉UserWordSeed342.values := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false]
    omega
  unfold UserLifecycleWord345.originalBase
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

variable (out input : Nat) (inside : Region input) (f : F → F)
variable (completion : ∀ (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F),
    HeaderRegisteredConstruction310.completed original c w initial out=
      f (RegisteredConstructorFrame309.prepared original c w input))

include inside completion

theorem original_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
     :
    UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w initial out=f (original input) := by
  change HeaderRegisteredConstruction310.completed
    (UserLifecycleWord345.originalBase (UserSubgroupSeed352.seed original w senderInitial receiverInitial) w) c w initial out= _
  rw [completion _ _ _ _,prepared_original original c w senderInitial receiverInitial input inside]

theorem completed_hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial out=f (original input) := by
  have bounds : 20934≤ input ∧ input<21199 := inside
  unfold AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment
  rw [original_frame out input inside f completion _ c w initial senderInitial receiverInitial,
    seeded_outside _ w input inside,
    AuthorizationPointSeed405.outside _ w authInitial input (by omega) (by omega)]
  exact congrArg f (AuthorizationSharedSeed416.outside original c w input (by omega))

theorem rk_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  have bounds : 20934≤ input ∧ input<21199 := inside
  let chosen := AuthorizationFixedDomain485.withGenerator c
  let fixed := AuthorizationFixedSeed487.seed (AuthorizationRkSeed505.seed original w rkInitial) w.auth.randomizer
  let dh := AuthorizationDhSeed473.seed fixed chosen w legal
  let traced := AuthorizationTraceSeed451.seed dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk
  have preserved := completed_hint out input inside f completion (IvkInverseSeed426.seed traced w)
    (ConcreteAuthorizationCrypto430.withOperations chosen) w authInitial initial senderInitial receiverInitial
  apply preserved.trans
  apply congrArg f
  rw [IvkInverseSeed426.outside traced w input (by omega)]
  dsimp only [traced]
  rw [AuthorizationTraceSeed451.outside dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk input (Or.inr (by omega))]
  have outside : dh input=fixed input := by
    simp only [dh,AuthorizationDhSeed473.seed,if_neg (show input≠3765 by omega)]
  apply outside.trans
  dsimp only [fixed]
  rw [AuthorizationFixedSeed487.outside (AuthorizationRkSeed505.seed original w rkInitial) w.auth.randomizer input (Or.inr (by omega))]
  simp only [AuthorizationRkSeed505.seed,if_neg (show input≠4271 by omega),
    if_neg (show ¬(4272≤ input ∧ input<4280) by omega)]

theorem retained_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    FixedFamilyBindings551.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  unfold FixedFamilyBindings551.assignment
  rw [rk_frame out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial]
  exact congrArg f (fixed_seed_outside original w input inside)

theorem payload_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    PayloadBindings565.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  unfold PayloadBindings565.assignment
  rw [retained_frame out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial]
  exact congrArg f (payload_seed_outside original c w legal input inside)

theorem retained_frame_full (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    PublishedInverseSeed592.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  unfold PublishedInverseSeed592.assignment PublishedPointSeed584.assignment
  rw [payload_frame out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial,
    published_seed_outside _ w input inside,inverse_seed_outside original w input inside]

theorem ownership_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    OwnershipBindings604.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  unfold OwnershipBindings604.assignment
  rw [retained_frame_full out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial,
    ownership_seed_outside original c w legal input inside]


theorem tier_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    TierBindings617.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  unfold TierBindings617.assignment
  rw [ownership_frame out input inside f completion _ (DetectionGroupDomain611.baseCrypto c) w legal rkInitial authInitial initial senderInitial receiverInitial]
  exact congrArg f (tier_seed_outside original c w legal input inside)

theorem flagged_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    TierFlagBindings630.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  have bounds : 20934≤ input ∧ input<21199 := inside
  unfold TierFlagBindings630.assignment
  rw [tier_frame out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial]
  exact congrArg f (TierFlagSeed623.outside original w input (Or.inr (by omega)))


theorem sign_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    BalanceSignBindings652.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  have bounds : 20934≤ input ∧ input<21199 := inside
  unfold BalanceSignBindings652.assignment
  rw [flagged_frame out input inside f completion _ c w legal rkInitial authInitial initial senderInitial receiverInitial]
  exact congrArg f (BalanceSignBindings652.outside original w input (by omega))

theorem blinding_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)  :
    BalanceBlindingBindings680.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial out=f (original input) := by
  have bounds : 20934≤ input ∧ input<21199 := inside
  unfold BalanceBlindingBindings680.assignment
  rw [sign_frame out input inside f completion _ (BalanceBlindingDomain670.withBlinding c) w legal rkInitial authInitial initial senderInitial receiverInitial]
  exact congrArg f (BalanceBlindingTrace675.outside original w.blinding input (Or.inl (by omega)))

end ShielddSecurity.MapFunctionalFrame719

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.seeded_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.seeded_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.fixed_seed_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.fixed_seed_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.payload_seed_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.payload_seed_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.published_seed_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.published_seed_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.inverse_seed_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.inverse_seed_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.ownership_seed_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.ownership_seed_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.tier_seed_outside
#print axioms ShielddSecurity.MapFunctionalFrame719.tier_seed_outside

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.prepared_original
#print axioms ShielddSecurity.MapFunctionalFrame719.prepared_original

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.original_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.original_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.completed_hint
#print axioms ShielddSecurity.MapFunctionalFrame719.completed_hint

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.rk_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.rk_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.retained_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.retained_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.payload_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.payload_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.retained_frame_full
#print axioms ShielddSecurity.MapFunctionalFrame719.retained_frame_full

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.ownership_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.ownership_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.tier_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.tier_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.flagged_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.flagged_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.sign_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.sign_frame

set_option pp.all true in
#check @ShielddSecurity.MapFunctionalFrame719.blinding_frame
#print axioms ShielddSecurity.MapFunctionalFrame719.blinding_frame
