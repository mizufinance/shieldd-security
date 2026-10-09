import ShielddSecurity.TransferEncryptionBranchCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferEncryptionDecomposition
open TransferCore TransferSem TransferEncryptionBranchCompletion

def MulZeroLaw (c : Crypto) : Prop := ∀ point, c.mul 0 point = ⟨0,1⟩

theorem fadd_fsub_cancel (ciphertext shared : Nat) (canonical : ciphertext < fieldModulus) :
    fadd (fsub ciphertext shared) shared = ciphertext := by
  have positive : 0 < fieldModulus := by decide
  have bound : shared % fieldModulus < fieldModulus := Nat.mod_lt _ positive
  unfold fadd fsub
  rw [Nat.mod_eq_of_lt canonical, Nat.add_mod]
  simp only [Nat.mod_mod]
  by_cases lower : shared % fieldModulus ≤ ciphertext
  · have rearrange : ciphertext+fieldModulus-shared%fieldModulus =
        ciphertext-shared%fieldModulus+fieldModulus := by omega
    have differenceBound : ciphertext-shared%fieldModulus < fieldModulus := by omega
    rw [rearrange,Nat.add_mod_right,Nat.mod_eq_of_lt differenceBound,
      Nat.sub_add_cancel lower,Nat.mod_eq_of_lt canonical]
  · have differenceBound : ciphertext+fieldModulus-shared%fieldModulus < fieldModulus := by omega
    rw [Nat.mod_eq_of_lt differenceBound]
    have cancel : ciphertext+fieldModulus-shared%fieldModulus+shared%fieldModulus =
        ciphertext+fieldModulus := by omega
    rw [cancel,Nat.add_mod_right,Nat.mod_eq_of_lt canonical]

def recover (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) : LegalEncryptionInputs c w where
  seeds := fun slot => fsub (w.encryption.tiers slot).c2
    (secret c (c.mul (w.encryption.tiers slot).ephemeral (selectedKey c w)))
  ephemeral := fun slot => (w.encryption.tiers slot).ephemeral
  ownershipRandomness := fun slot => (w.encryption.ownership slot).randomness
  seedCanonical := fun _ => fsub_canonical _ _
  ephemeralBounded := fun slot => (sem.2.2.2.2.2.2.1 slot).1
  ephemeralNonzero := by
    intro slot zero
    have tier := sem.2.2.2.2.2.2.1 slot
    apply tier.2.2.1
    rw [tier.2.1,zero,zeroMul]
  ownershipBounded := fun slot => (sem.2.2.2.2.2.2.2 slot).1
  ownershipNonzero := by
    intro slot zero
    have owner := sem.2.2.2.2.2.2.2 slot
    apply owner.2.2.1
    rw [owner.2.1,zero,zeroMul]
  epkNonidentity := by
    intro slot
    have tier := sem.2.2.2.2.2.2.1 slot
    rw [←tier.2.1]
    exact tier.2.2.1
  ownershipNonidentity := by
    intro slot
    have owner := sem.2.2.2.2.2.2.2 slot
    rw [←owner.2.1]
    exact owner.2.2.1
  detectionNonidentity := sem.1
  checkingNonidentity := (sem.2.2.2.2.2.2.2 0).2.2.2.1

theorem canonical_encryption_fields (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    fieldsCanonical (encryptionFields w.encryption) := by
  intro value member
  exact canonical value (List.mem_append.mpr (Or.inr member))

theorem canonical_c2 (w : TransferSem.Witness) (canonical : CanonicalWitness w) (slot : Fin 4) :
    (w.encryption.tiers slot).c2 < fieldModulus := by
  apply canonical_encryption_fields w canonical
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨slot,List.mem_finRange slot,?_⟩
  simp [pointFields]

theorem recovered_c2 (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) (slot : Fin 4) :
    (constructTier c w (recover c w zeroMul sem) slot).c2 = (w.encryption.tiers slot).c2 := by
  exact fadd_fsub_cancel _ _ (canonical_c2 w canonical slot)

theorem recovered_tier_public (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) (slot : Fin 4) :
    let made := constructTier c w (recover c w zeroMul sem) slot
    let old := w.encryption.tiers slot
    made.epk = old.epk ∧ made.c2 = old.c2 ∧
    (if slot.val=0 ∨ slot.val=2 then made.confirmation=old.confirmation ∧
      made.ciphertext 0=old.ciphertext 0 else ∀ j, made.ciphertext j=old.ciphertext j) := by
  dsimp only
  have tier := sem.2.2.2.2.2.2.1 slot
  refine ⟨tier.2.1.symm,recovered_c2 c w zeroMul sem canonical slot,?_⟩
  have equation := tier.2.2.2
  by_cases core : slot.val=0 ∨ slot.val=2
  · simp only [if_pos core] at equation ⊢
    constructor
    · simp only [constructTier,recover,if_pos core]
      rw [←tier.2.1]
      exact equation.1.symm
    · simpa only [constructTier,recover,if_pos core] using equation.2.symm
  · simp only [if_neg core] at equation ⊢
    intro j
    simpa only [constructTier,recover,if_neg core] using (equation j).symm

def PublicEncryptionAgreement (made old : Encryption) : Prop :=
  made.timestamp=old.timestamp ∧ made.auditEpoch=old.auditEpoch ∧
  (∀ slot, made.detection slot=old.detection slot) ∧
  (∀ slot, made.policy slot=old.policy slot) ∧ (∀ slot, made.salts slot=old.salts slot) ∧
  (∀ slot : Fin 4, (made.tiers slot).epk=(old.tiers slot).epk ∧
    (made.tiers slot).c2=(old.tiers slot).c2 ∧
    (if slot.val=0 ∨ slot.val=2 then (made.tiers slot).confirmation=(old.tiers slot).confirmation ∧
      (made.tiers slot).ciphertext 0=(old.tiers slot).ciphertext 0
     else ∀ j, (made.tiers slot).ciphertext j=(old.tiers slot).ciphertext j)) ∧
  (∀ slot : Fin 2, (made.ownership slot).r=(old.ownership slot).r ∧
    (made.ownership slot).c=(old.ownership slot).c)

theorem recovered_public_agreement (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) :
    PublicEncryptionAgreement (construct c w (recover c w zeroMul sem)) w.encryption := by
  refine ⟨sem.2.1.symm,sem.2.2.1.symm,?_,?_,?_,?_,?_⟩
  · intro slot
    have det := sem.2.2.2.2.2.1 slot
    have epk : (w.encryption.tiers 0).epk = c.mul (w.encryption.tiers 0).ephemeral c.generator :=
      (sem.2.2.2.2.2.2.1 0).2.1
    simp only [construct,detectionSeed,recover]
    rw [←epk]
    exact det.symm
  · intro slot
    exact (sem.2.2.2.1 slot).symm
  · intro slot
    exact (sem.2.2.2.2.1 slot).symm
  · intro slot
    exact recovered_tier_public c w zeroMul sem canonical slot
  · intro slot
    have owner := sem.2.2.2.2.2.2.2 slot
    exact ⟨owner.2.1.symm,owner.2.2.2.2.symm⟩

-- Transfer's public encryption projection; inactive private auxiliaries are excluded.
def statementEncryptionFields (e : Encryption) : List Nat :=
  let a := e.tiers 0; let b := e.tiers 1; let d := e.tiers 2; let f := e.tiers 3
  [e.detection 0,e.detection 1,e.detection 2,e.detection 3,
   a.epk.x,a.epk.y,a.c2,a.ciphertext 0,b.epk.x,b.epk.y,b.c2,b.ciphertext 0,b.ciphertext 1,b.ciphertext 2,
   d.epk.x,d.epk.y,d.c2,d.ciphertext 0,f.epk.x,f.epk.y,f.c2,f.ciphertext 0,f.ciphertext 1,f.ciphertext 2,
   e.timestamp,a.confirmation,d.confirmation,e.policy 0,e.policy 1,e.policy 2,e.policy 3,
   e.salts 0,e.salts 1,e.salts 2,e.salts 3,e.auditEpoch,
   (e.ownership 0).r.x,(e.ownership 0).r.y,(e.ownership 0).c.x,(e.ownership 0).c.y,
   (e.ownership 1).r.x,(e.ownership 1).r.y,(e.ownership 1).c.x,(e.ownership 1).c.y]

theorem statement_encryption_fields_length (e : Encryption) : (statementEncryptionFields e).length=44 := rfl

theorem agreement_statement_fields (made old : Encryption) (agreement : PublicEncryptionAgreement made old) :
    statementEncryptionFields made=statementEncryptionFields old := by
  rcases agreement with ⟨timestamp,epoch,det,policy,salts,tiers,owners⟩
  have epk := fun slot => (tiers slot).1
  have c2 := fun slot => (tiers slot).2.1
  have core0 : (made.tiers 0).confirmation=(old.tiers 0).confirmation ∧
      (made.tiers 0).ciphertext 0=(old.tiers 0).ciphertext 0 := by simpa using (tiers 0).2.2
  have core2 : (made.tiers 2).confirmation=(old.tiers 2).confirmation ∧
      (made.tiers 2).ciphertext 0=(old.tiers 2).ciphertext 0 := by simpa using (tiers 2).2.2
  have ext1 : ∀ j, (made.tiers 1).ciphertext j=(old.tiers 1).ciphertext j := by simpa using (tiers 1).2.2
  have ext3 : ∀ j, (made.tiers 3).ciphertext j=(old.tiers 3).ciphertext j := by simpa using (tiers 3).2.2
  have ownerR := fun slot => (owners slot).1
  have ownerC := fun slot => (owners slot).2
  simp only [statementEncryptionFields,timestamp,epoch,det,policy,salts,epk,c2,core0.1,core0.2,
    core2.1,core2.2,ext1,ext3,ownerR,ownerC]

def nonEncryptionFields (c : Crypto) (w : TransferSem.Witness) : List Nat :=
  let net := balance c w
  [w.auth.rk.x,w.auth.rk.y,w.anchor,(w.outputs 0).noteCommitment,(w.outputs 0).recovery.commitment,
   (w.outputs 1).noteCommitment,(w.outputs 1).recovery.commitment,net.x,net.y,
   w.routing.tags 0,w.routing.tags 1,w.routing.parameterSet,w.volume.nullifier,w.volume.commitment,
   w.volume.dayStart,w.volume.context,(w.spends 0).nullifier,(w.spends 1).nullifier,w.assetAnchor,w.userAnchor]

theorem public_fields_split (c : Crypto) (w : TransferSem.Witness) :
    publicFields c w=nonEncryptionFields c w ++ statementEncryptionFields {w.encryption with timestamp:=w.timestamp} := rfl

theorem agreement_all64 (c : Crypto) (w : TransferSem.Witness) (made : Encryption)
    (agreement : PublicEncryptionAgreement made w.encryption) :
    publicFields c {w with encryption:=made}=publicFields c w := by
  rw [public_fields_split,public_fields_split]
  change nonEncryptionFields c w ++ statementEncryptionFields {made with timestamp:=w.timestamp}=
    nonEncryptionFields c w ++ statementEncryptionFields {w.encryption with timestamp:=w.timestamp}
  rw [agreement_statement_fields {made with timestamp:=w.timestamp}
    {w.encryption with timestamp:=w.timestamp} ⟨rfl,agreement.2⟩]

def normalizedWitness (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) : TransferSem.Witness :=
  {w with encryption:=construct c w (recover c w zeroMul sem)}

theorem recovered_public44 (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) :
    statementEncryptionFields (normalizedWitness c w zeroMul sem).encryption=
      statementEncryptionFields w.encryption :=
  agreement_statement_fields _ _ (recovered_public_agreement c w zeroMul sem canonical)

theorem recovered_all64 (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) :
    publicFields c (normalizedWitness c w zeroMul sem)=publicFields c w :=
  agreement_all64 _ _ _ (recovered_public_agreement c w zeroMul sem canonical)

theorem recovered_statement_hash (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) :
    c.hash .transferStatement (publicFields c (normalizedWitness c w zeroMul sem))=
      c.hash .transferStatement (publicFields c w) := by rw [recovered_all64 c w zeroMul sem canonical]

theorem recovered_committed_blinding (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) : (normalizedWitness c w zeroMul sem).blinding=w.blinding := rfl

theorem recovered_full_frame (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) : {(normalizedWitness c w zeroMul sem) with encryption:=w.encryption}=w :=
  restore_full_record c w (recover c w zeroMul sem)

theorem inactive_core_ciphertext_zero (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (slot : Fin 4) (core : slot.val=0 ∨ slot.val=2)
    (j : Fin 3) (unused : j.val≠0) : ((normalizedWitness c w zeroMul sem).encryption.tiers slot).ciphertext j=0 := by
  simp only [normalizedWitness,construct,constructTier,if_pos core,if_neg unused]

theorem inactive_extended_confirmation_zero (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (slot : Fin 4) (extended : ¬(slot.val=0 ∨ slot.val=2)) :
    ((normalizedWitness c w zeroMul sem).encryption.tiers slot).confirmation=0 := by
  simp only [normalizedWitness,construct,constructTier,if_neg extended]

theorem recovered_canonical_semantics (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) (crypto : CanonicalCrypto c) :
    CanonicalWitness (normalizedWitness c w zeroMul sem) ∧ EncryptionSem c (normalizedWitness c w zeroMul sem) :=
  constructed_canonical_encryption_semantics c w (recover c w zeroMul sem) canonical crypto

theorem recovered_ephemeral_preserved (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (slot : Fin 4) :
    ((normalizedWitness c w zeroMul sem).encryption.tiers slot).ephemeral=(w.encryption.tiers slot).ephemeral := rfl

theorem recovered_ownership_randomness_preserved (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (slot : Fin 2) :
    ((normalizedWitness c w zeroMul sem).encryption.ownership slot).randomness=(w.encryption.ownership slot).randomness := rfl

theorem representation_exists (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : EncryptionSem c w) (canonical : CanonicalWitness w) (crypto : CanonicalCrypto c) :
    ∃ i : LegalEncryptionInputs c w,
      CanonicalWitness {w with encryption:=construct c w i} ∧
      EncryptionSem c {w with encryption:=construct c w i} ∧
      publicFields c {w with encryption:=construct c w i}=publicFields c w ∧
      ({w with encryption:=construct c w i} : TransferSem.Witness).blinding=w.blinding := by
  refine ⟨recover c w zeroMul sem,?_,?_,recovered_all64 c w zeroMul sem canonical,rfl⟩
  · exact (recovered_canonical_semantics c w zeroMul sem canonical crypto).1
  · exact (recovered_canonical_semantics c w zeroMul sem canonical crypto).2

theorem semantic_transfer_normalization (c : Crypto) (w : TransferSem.Witness) (zeroMul : MulZeroLaw c)
    (sem : TransferSem.TransferSem c w) (crypto : CanonicalCrypto c) :
    ∃ i : LegalEncryptionInputs c w,
      TransferSem.TransferSem c {w with encryption:=construct c w i} ∧
      publicFields c {w with encryption:=construct c w i}=publicFields c w ∧
      ({w with encryption:=construct c w i} : TransferSem.Witness).blinding=w.blinding := by
  rcases sem with ⟨canonical,components,published⟩
  rcases components with ⟨registry,sender,receiver,auth,spends,outputs,volume,routing,encryption,balance⟩
  let i := recover c w zeroMul encryption
  have formed := recovered_canonical_semantics c w zeroMul encryption canonical crypto
  refine ⟨i,⟨formed.1,?_,?_⟩,recovered_all64 c w zeroMul encryption canonical,rfl⟩
  · exact ⟨registry,sender,receiver,auth,spends,outputs,volume,routing,formed.2,balance⟩
  · rw [show publicFields c {w with encryption:=construct c w i}=publicFields c w from
      recovered_all64 c w zeroMul encryption canonical]
    exact published

-- Canonical input is necessary for inverse cancellation, not an assumed output equation.
theorem inverse_requires_canonical (ciphertext shared : Nat)
    (inverse : fadd (fsub ciphertext shared) shared=ciphertext) : ciphertext<fieldModulus := by
  rw [←inverse]
  exact fadd_canonical _ _

theorem refuse_noncanonical_inverse (ciphertext shared : Nat) (invalid : fieldModulus≤ciphertext) :
    fadd (fsub ciphertext shared) shared≠ciphertext := by
  intro inverse
  exact Nat.not_lt_of_ge invalid (inverse_requires_canonical ciphertext shared inverse)

-- A public-preserving inactive mutation is a semantic control against whole-private-record equality.
def inactiveVariant (e : Encryption) (value : Nat) : Encryption :=
  {e with tiers:=fun slot => if slot=0 then
    {e.tiers slot with ciphertext:=fun j => if j=1 then value else (e.tiers slot).ciphertext j}
    else e.tiers slot}

theorem inactive_variant_agreement (e : Encryption) (value : Nat) :
    PublicEncryptionAgreement (inactiveVariant e value) e := by
  refine ⟨rfl,rfl,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),?_,(fun _ => ⟨rfl,rfl⟩)⟩
  intro slot
  by_cases zeroSlot : slot=0
  · subst slot
    simp [inactiveVariant]
  · simp [inactiveVariant,zeroSlot]

theorem inactive_variant_public44 (e : Encryption) (value : Nat) :
    statementEncryptionFields (inactiveVariant e value)=statementEncryptionFields e :=
  agreement_statement_fields _ _ (inactive_variant_agreement e value)

theorem inactive_variant_all64 (c : Crypto) (w : TransferSem.Witness) (value : Nat) :
    publicFields c {w with encryption:=inactiveVariant w.encryption value}=publicFields c w :=
  agreement_all64 _ _ _ (inactive_variant_agreement w.encryption value)

theorem inactive_variant_distinct (e : Encryption) (value : Nat)
    (changed : value≠(e.tiers 0).ciphertext 1) : inactiveVariant e value≠e := by
  intro equal
  apply changed
  have field := congrArg (fun enc : Encryption => (enc.tiers 0).ciphertext 1) equal
  simpa [inactiveVariant] using field

theorem inactive_variant_semantics (c : Crypto) (w : TransferSem.Witness) (value : Nat)
    (sem : EncryptionSem c w) : EncryptionSem c {w with encryption:=inactiveVariant w.encryption value} := by
  refine ⟨sem.1,sem.2.1,sem.2.2.1,sem.2.2.2.1,sem.2.2.2.2.1,sem.2.2.2.2.2.1,?_,sem.2.2.2.2.2.2.2⟩
  intro slot
  by_cases zeroSlot : slot=0
  · subst slot
    simpa [inactiveVariant] using sem.2.2.2.2.2.2.1 0
  · simpa only [inactiveVariant,if_neg zeroSlot] using sem.2.2.2.2.2.2.1 slot

set_option pp.all true in
#check @recover
#print axioms recover
set_option pp.all true in
#check @fadd_fsub_cancel
#print axioms fadd_fsub_cancel
set_option pp.all true in
#check @canonical_encryption_fields
#print axioms canonical_encryption_fields
set_option pp.all true in
#check @canonical_c2
#print axioms canonical_c2
set_option pp.all true in
#check @recovered_c2
#print axioms recovered_c2
set_option pp.all true in
#check @recovered_tier_public
#print axioms recovered_tier_public
set_option pp.all true in
#check @recovered_public_agreement
#print axioms recovered_public_agreement
set_option pp.all true in
#check @statement_encryption_fields_length
#print axioms statement_encryption_fields_length
set_option pp.all true in
#check @agreement_statement_fields
#print axioms agreement_statement_fields
set_option pp.all true in
#check @public_fields_split
#print axioms public_fields_split
set_option pp.all true in
#check @agreement_all64
#print axioms agreement_all64
set_option pp.all true in
#check @recovered_public44
#print axioms recovered_public44
set_option pp.all true in
#check @recovered_all64
#print axioms recovered_all64
set_option pp.all true in
#check @recovered_statement_hash
#print axioms recovered_statement_hash
set_option pp.all true in
#check @recovered_committed_blinding
#print axioms recovered_committed_blinding
set_option pp.all true in
#check @recovered_full_frame
#print axioms recovered_full_frame
set_option pp.all true in
#check @inactive_core_ciphertext_zero
#print axioms inactive_core_ciphertext_zero
set_option pp.all true in
#check @inactive_extended_confirmation_zero
#print axioms inactive_extended_confirmation_zero
set_option pp.all true in
#check @recovered_canonical_semantics
#print axioms recovered_canonical_semantics
set_option pp.all true in
#check @recovered_ephemeral_preserved
#print axioms recovered_ephemeral_preserved
set_option pp.all true in
#check @recovered_ownership_randomness_preserved
#print axioms recovered_ownership_randomness_preserved
set_option pp.all true in
#check @representation_exists
#print axioms representation_exists
set_option pp.all true in
#check @semantic_transfer_normalization
#print axioms semantic_transfer_normalization
set_option pp.all true in
#check @inverse_requires_canonical
#print axioms inverse_requires_canonical
set_option pp.all true in
#check @refuse_noncanonical_inverse
#print axioms refuse_noncanonical_inverse
set_option pp.all true in
#check @inactive_variant_agreement
#print axioms inactive_variant_agreement
set_option pp.all true in
#check @inactive_variant_public44
#print axioms inactive_variant_public44
set_option pp.all true in
#check @inactive_variant_all64
#print axioms inactive_variant_all64
set_option pp.all true in
#check @inactive_variant_distinct
#print axioms inactive_variant_distinct
set_option pp.all true in
#check @inactive_variant_semantics
#print axioms inactive_variant_semantics
end ShielddSecurity.TransferEncryptionDecomposition
