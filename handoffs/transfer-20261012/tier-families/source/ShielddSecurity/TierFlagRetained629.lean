import ShielddSecurity.TierFlagSemanticFrame628
import ShielddSecurity.TierBindings617
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagRetained629
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierFlagLayout620 (columns flags)

theorem rk_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  let chosen := AuthorizationFixedDomain485.withGenerator c
  let fixed := AuthorizationFixedSeed487.seed (AuthorizationRkSeed505.seed original w rkInitial) w.auth.randomizer
  let dh := AuthorizationDhSeed473.seed fixed chosen w legal
  let traced := AuthorizationTraceSeed451.seed dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk
  have preserved : IvkInverseSeed426.seed traced w column=original column := by
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
  exact (TierFlagSemanticFrame628.authorization_frame (IvkInverseSeed426.seed traced w)
    (ConcreteAuthorizationCrypto430.withOperations chosen) w authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem fixed_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (member : column∈columns) :
    FixedFamilySeed549.seed original w column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  simp only [FixedFamilySeed549.seed,FixedFamilySeed549.one,
    if_neg (show ¬(16406≤column ∧ column<16406+252) by omega),
    if_neg (show ¬(15144≤column ∧ column<15144+252) by omega),
    if_neg (show ¬(13882≤column ∧ column<13882+252) by omega),
    if_neg (show ¬(11864≤column ∧ column<11864+252) by omega),
    if_neg (show ¬(10336≤column ∧ column<10336+252) by omega),
    if_neg (show ¬(8804≤column ∧ column<8804+252) by omega),
    if_neg (show ¬(6587≤column ∧ column<6587+252) by omega),
    if_neg (show ¬(5183≤column ∧ column<5183+252) by omega)]

theorem fixed_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    FixedFamilyBindings551.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := fixed_seed_outside original w column member
  unfold FixedFamilyBindings551.assignment
  exact (rk_frame (FixedFamilySeed549.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem payload_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (column : Nat) (member : column∈columns) :
    PayloadTraceSeed564.seed original c w legal column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  simp only [PayloadTraceSeed564.seed,PayloadTraceSeed564.one,
    if_neg (show ¬(5436≤column ∧ column<5436+756) by omega),
    if_neg (show ¬(6840≤column ∧ column<6840+756) by omega)]

theorem payload_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    PayloadBindings565.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := payload_seed_outside original c w legal column member
  unfold PayloadBindings565.assignment
  exact (fixed_frame (PayloadTraceSeed564.seed original c w legal) c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem published_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (member : column∈columns) :
    PublishedPointSeed584.seed original w column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  unfold PublishedPointSeed584.seed
  split <;> first | rfl | (exfalso; omega)

theorem published_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    PublishedPointSeed584.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := published_seed_outside original w column member
  unfold PublishedPointSeed584.assignment
  exact (payload_frame (PublishedPointSeed584.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem inverse_seed_outside (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (member : column∈columns) :
    PublishedInverseSeed592.seed original w column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  unfold PublishedInverseSeed592.seed
  split <;> first | rfl | (exfalso; omega)

theorem inverse_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    PublishedInverseSeed592.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := inverse_seed_outside original w column member
  unfold PublishedInverseSeed592.assignment
  exact (published_frame (PublishedInverseSeed592.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem ownership_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (column : Nat) (member : column∈columns) :
    OwnershipTrace603.seed original c w legal column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  unfold OwnershipTrace603.seed
  rw [OwnershipTrace603.one_outside _ _ _ 9322 _ (Or.inl (by omega)),
    OwnershipTrace603.one_outside _ _ _ 10854 _ (Or.inl (by omega))]

theorem ownership_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    OwnershipBindings604.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := ownership_seed_outside original c w legal column member
  unfold OwnershipBindings604.assignment
  exact (inverse_frame (OwnershipTrace603.seed original c w legal) c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem tier_seed_outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (column : Nat) (member : column∈columns) : TierTrace616.seed original c w legal column=original column := by
  have bounds := TierFlagLayout620.bounds column member
  unfold TierTrace616.seed
  rw [TierTrace616.one_outside _ _ _ 12117 _ (Or.inl (by omega)),
    TierTrace616.one_outside _ _ _ 12873 _ (Or.inl (by omega)),
    TierTrace616.one_outside _ _ _ 14135 _ (Or.inl (by omega)),
    TierTrace616.one_outside _ _ _ 15397 _ (Or.inl (by omega)),
    TierTrace616.one_outside _ _ _ 16659 _ (Or.inl (by omega))]

theorem tier_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    TierBindings617.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have preserved := tier_seed_outside original c w legal column member
  unfold TierBindings617.assignment
  exact (ownership_frame (TierTrace616.seed original c w legal) (DetectionGroupDomain611.baseCrypto c)
    w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

end ShielddSecurity.TierFlagRetained629

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.rk_frame
#print axioms ShielddSecurity.TierFlagRetained629.rk_frame

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.fixed_seed_outside
#print axioms ShielddSecurity.TierFlagRetained629.fixed_seed_outside

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.fixed_frame
#print axioms ShielddSecurity.TierFlagRetained629.fixed_frame

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.payload_seed_outside
#print axioms ShielddSecurity.TierFlagRetained629.payload_seed_outside

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.payload_frame
#print axioms ShielddSecurity.TierFlagRetained629.payload_frame

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.published_seed_outside
#print axioms ShielddSecurity.TierFlagRetained629.published_seed_outside

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.published_frame
#print axioms ShielddSecurity.TierFlagRetained629.published_frame

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.inverse_seed_outside
#print axioms ShielddSecurity.TierFlagRetained629.inverse_seed_outside

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.inverse_frame
#print axioms ShielddSecurity.TierFlagRetained629.inverse_frame

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.ownership_seed_outside
#print axioms ShielddSecurity.TierFlagRetained629.ownership_seed_outside

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.ownership_frame
#print axioms ShielddSecurity.TierFlagRetained629.ownership_frame

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.tier_seed_outside
#print axioms ShielddSecurity.TierFlagRetained629.tier_seed_outside

set_option pp.all true in
#check @ShielddSecurity.TierFlagRetained629.tier_frame
#print axioms ShielddSecurity.TierFlagRetained629.tier_frame
