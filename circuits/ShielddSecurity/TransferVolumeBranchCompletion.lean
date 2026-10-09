import ShielddSecurity.TransferSem

set_option maxHeartbeats 400000

/-! Original parameterized volume construction for the exact maintained semantic
contract (TransferSem SHA256 34bfad86d8619e505f0cfcd7e1191708be5524146a86fc2bdfda444c3f53ab72).
No result VolumeSem or selected output equation is assumed. The authenticated
predecessor path is an input prerequisite; hash interpretation and compiled-row
refinement remain separate. All non-volume fields are preserved definitionally. -/
namespace ShielddSecurity.TransferVolumeBranchCompletion
open TransferCore TransferSem

structure Inputs where
  context : Nat
  useReal : Bool
  startsNewDay : Bool
  dayIndex : Nat
  second : Nat
  prior : Nat
  priorBlinding : Nat
  priorPosition : Nat
  priorSiblings : Path 24
  successorBlinding : Nat

def selectedDay (i : Inputs) : Nat := if i.context = 1 then 86400 * i.dayIndex else 0

def selectedSubject (c : Crypto) (base : TransferSem.Witness) : Nat :=
  c.hash .volumeSubject (addressFields base.sender.address ++ [base.asset])

def predecessor (c : Crypto) (base : TransferSem.Witness) (i : Inputs) : Nat :=
  volumeState c (selectedSubject c base) (selectedDay i) i.prior i.priorBlinding

/-- Legal input data and independent prerequisites. The continuation premise
 authenticates the computed predecessor at the supplied anchor. No premise fixes
 the constructed subject, successor, nullifier, commitment or dayStart. -/
structure LegalVolumeInputs (c : Crypto) (base : TransferSem.Witness) extends Inputs where
  timestampBound : base.timestamp < 2 ^ 64
  dayBound : dayIndex < 2 ^ 48
  secondBound : second ≤ 86399
  timeSplit : base.timestamp = 86400 * dayIndex + second
  contextValid : context = 1 ∨ context = 2
  feeSelf : context = 2 → external base = false
  trackedEligible : useReal = true → context = 1 ∧ base.regulated = true ∧ external base = true
  priorBound : prior < amountBound
  outboundPositive : 0 < (base.outputs 0).amount
  outboundBound : (base.outputs 0).amount < amountBound
  candidateBound : prior + (base.outputs 0).amount < amountBound
  limitBound : base.registry.dailyLimit < amountBound
  positionBound : priorPosition < 2 ^ 48
  trackedLimit : useReal = true → prior + (base.outputs 0).amount ≤ base.registry.dailyLimit
  originZero : useReal = true → startsNewDay = true → prior = 0
  continuationAuthenticated : useReal = true → startsNewDay = false →
    root c .state priorPosition
      (volumeState c (selectedSubject c base)
        (if context = 1 then 86400 * dayIndex else 0) prior priorBlinding)
      priorSiblings = base.anchor

def construct (c : Crypto) (base : TransferSem.Witness) (i : LegalVolumeInputs c base) : Volume :=
  let day := selectedDay i.toInputs
  let subject := selectedSubject c base
  let priorHead := predecessor c base i.toInputs
  let successor := if i.useReal then i.prior + (base.outputs 0).amount else 0
  let realNF := if i.startsNewDay then
    c.hash .volumeOriginNullifier [base.auth.nk, subject, day]
    else c.hash .noteNullifier [base.auth.nk, priorHead, i.priorPosition]
  let padding := [base.auth.nk, base.nonce, day]
  { context := i.context, useReal := i.useReal, startsNewDay := i.startsNewDay
    dayIndex := i.dayIndex, second := i.second, dayStart := day
    subject := subject, prior := i.prior, priorBlinding := i.priorBlinding
    priorCommitment := priorHead, priorPosition := i.priorPosition
    priorSiblings := i.priorSiblings, successor := successor
    successorBlinding := i.successorBlinding
    nullifier := if i.context = 2 then 0 else if i.useReal then realNF
      else c.hash .volumePaddingNullifier padding
    commitment := if i.context = 2 then 0 else if i.useReal then
      volumeState c subject day successor i.successorBlinding
      else c.hash .volumePaddingCommitment padding }

theorem constructed_volume_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) :
    VolumeSem c { base with volume := construct c base i } := by
  change base.timestamp < 2 ^ 64 ∧ i.dayIndex < 2 ^ 48 ∧ i.second ≤ 86399 ∧
    base.timestamp = 86400 * i.dayIndex + i.second ∧
    (i.context = 1 ∨ i.context = 2) ∧
    (i.context = 2 → external base = false) ∧
    selectedDay i.toInputs = (if i.context = 1 then 86400 * i.dayIndex else 0) ∧
    i.prior < amountBound ∧
    (if i.useReal then i.prior + (base.outputs 0).amount else 0) < amountBound ∧
    base.registry.dailyLimit < amountBound ∧
    i.prior + (base.outputs 0).amount < amountBound ∧ i.priorPosition < 2 ^ 48 ∧
    (i.useReal = true →
      (decide (i.context = 1) && base.regulated && external base) = true ∧
      selectedSubject c base = selectedSubject c base ∧
      (if i.useReal then i.prior + (base.outputs 0).amount else 0) =
        i.prior + (base.outputs 0).amount ∧
      (if i.useReal then i.prior + (base.outputs 0).amount else 0) ≤ base.registry.dailyLimit ∧
      (if i.startsNewDay then i.prior = 0 else
        predecessor c base i.toInputs = predecessor c base i.toInputs ∧
        root c .state i.priorPosition (predecessor c base i.toInputs) i.priorSiblings = base.anchor)) ∧
    (construct c base i).nullifier = (construct c base i).nullifier ∧
    (construct c base i).commitment = (construct c base i).commitment
  have successorBound : (if i.useReal then i.prior + (base.outputs 0).amount else 0) < amountBound := by
    cases h : i.useReal
    · simp [amountBound]
    · simpa [h] using i.candidateBound
  refine ⟨i.timestampBound, i.dayBound, i.secondBound, i.timeSplit, i.contextValid,
    i.feeSelf, rfl, i.priorBound, successorBound, i.limitBound, i.candidateBound,
    i.positionBound, ?_, rfl, rfl⟩
  intro tracked
  obtain ⟨ordinary, regulated, external⟩ := i.trackedEligible tracked
  refine ⟨by simp [ordinary, regulated, external], rfl, by simp [tracked],
    by simpa [tracked] using i.trackedLimit tracked, ?_⟩
  cases origin : i.startsNewDay
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨True.intro, i.continuationAuthenticated tracked origin⟩
  · simpa [origin] using i.originZero tracked origin

theorem nonvolume_fields_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) :
    let w := {base with volume := construct c base i}
    w.anchor = base.anchor ∧ w.asset = base.asset ∧ w.sender = base.sender ∧
    w.receiver = base.receiver ∧ w.auth = base.auth ∧ w.outputs = base.outputs ∧
    w.spends = base.spends ∧ w.blinding = base.blinding ∧ w.nonce = base.nonce ∧
    w.registry = base.registry ∧ w.routing = base.routing ∧ w.encryption = base.encryption := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) :
    { {base with volume := construct c base i} with volume := base.volume } = base := by
  cases base
  rfl

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical, List.mem_append, or_imp, forall_and]

theorem canonical_constructed_volume_fields (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (cryptoCanonical : CanonicalCrypto c)
    (priorBlindingCanonical : i.priorBlinding < fieldModulus)
    (successorBlindingCanonical : i.successorBlinding < fieldModulus)
    (siblingsCanonical : fieldsCanonical (pathFields i.priorSiblings)) :
    fieldsCanonical (volumeFields (construct c base i)) := by
  have hashCanonical := cryptoCanonical.1
  have amountField : amountBound < fieldModulus := by decide
  have timeField : 2^64 < fieldModulus := by decide
  have dayField : 2^48 < fieldModulus := by decide
  have zeroField : 0 < fieldModulus := by decide
  have priorCanonical := Nat.lt_trans i.priorBound amountField
  have dayIndexCanonical := Nat.lt_trans i.dayBound dayField
  have secondCanonical : i.second < fieldModulus := by
    have hb := i.secondBound
    unfold fieldModulus
    omega
  have contextCanonical : i.context < fieldModulus := by
    rcases i.contextValid with h | h <;> simp [h, fieldModulus]
  have dayCanonical : selectedDay i.toInputs < fieldModulus := by
    unfold selectedDay
    split
    · have ht := Nat.lt_trans i.timestampBound timeField
      have splitTime := i.timeSplit
      omega
    · exact zeroField
  have successorCanonical : (construct c base i).successor < fieldModulus := by
    change (if i.useReal then i.prior + (base.outputs 0).amount else 0) < fieldModulus
    split
    · exact Nat.lt_trans i.candidateBound amountField
    · exact zeroField
  have subjectCanonical : selectedSubject c base < fieldModulus := hashCanonical _ _
  have headCanonical : predecessor c base i.toInputs < fieldModulus := hashCanonical _ _
  have positionCanonical := Nat.lt_trans i.positionBound dayField
  have nullifierCanonical : (construct c base i).nullifier < fieldModulus := by
    dsimp only [construct]
    split
    · exact zeroField
    · split
      · split <;> exact hashCanonical _ _
      · exact hashCanonical _ _
  have commitmentCanonical : (construct c base i).commitment < fieldModulus := by
    dsimp only [construct]
    split
    · exact zeroField
    · split <;> exact hashCanonical _ _
  unfold volumeFields
  apply (fieldsCanonical_append _ _).mpr
  refine ⟨?_, siblingsCanonical⟩
  simp only [fieldsCanonical, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true, construct]
  exact ⟨nullifierCanonical, commitmentCanonical, dayCanonical, contextCanonical,
    dayIndexCanonical, secondCanonical, subjectCanonical, priorCanonical,
    priorBlindingCanonical, headCanonical, positionCanonical, successorCanonical,
    successorBlindingCanonical⟩

/-- Complete canonical witness frame: replaces the volume block, preserving
 every other field including audit, optional padding and inactive auxiliaries. -/
theorem canonical_witness_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c)
    (priorBlindingCanonical : i.priorBlinding < fieldModulus)
    (successorBlindingCanonical : i.successorBlinding < fieldModulus)
    (siblingsCanonical : fieldsCanonical (pathFields i.priorSiblings)) :
    CanonicalWitness {base with volume := construct c base i} := by
  have volumeCanonical := canonical_constructed_volume_fields c base i cryptoCanonical
    priorBlindingCanonical successorBlindingCanonical siblingsCanonical
  simp only [CanonicalWitness, fieldsCanonical_append] at baseCanonical ⊢
  exact ⟨⟨baseCanonical.1.1, volumeCanonical⟩, baseCanonical.2⟩

theorem fee_cannot_track (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (fee : i.context = 2) : i.useReal = false := by
  cases real : i.useReal
  · rfl
  · have ordinary := (i.trackedEligible real).1
    omega

theorem external_requires_ordinary (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (ext : external base = true) : i.context = 1 := by
  rcases i.contextValid with ordinary | fee
  · exact ordinary
  · have self := i.feeSelf fee
    simp [ext] at self

theorem constructed_fee_payload (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (fee : i.context = 2) :
    (construct c base i).nullifier = 0 ∧ (construct c base i).commitment = 0 ∧
    (construct c base i).dayStart = 0 ∧ (construct c base i).useReal = false := by
  have real := fee_cannot_track c base i fee
  simp [construct, selectedDay, fee, real]

theorem constructed_origin_payload (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (real : i.useReal = true) (origin : i.startsNewDay = true) :
    (construct c base i).nullifier = c.hash .volumeOriginNullifier
      [base.auth.nk, selectedSubject c base, 86400*i.dayIndex] ∧
    (construct c base i).commitment = volumeState c (selectedSubject c base)
      (86400*i.dayIndex) (i.prior+(base.outputs 0).amount) i.successorBlinding := by
  have ordinary := (i.trackedEligible real).1
  simp [construct, selectedDay, ordinary, real, origin]

theorem constructed_continuation_payload (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (real : i.useReal = true) (cont : i.startsNewDay = false) :
    (construct c base i).nullifier = c.hash .noteNullifier
      [base.auth.nk, predecessor c base i.toInputs, i.priorPosition] ∧
    (construct c base i).commitment = volumeState c (selectedSubject c base)
      (86400*i.dayIndex) (i.prior+(base.outputs 0).amount) i.successorBlinding := by
  have ordinary := (i.trackedEligible real).1
  simp [construct, selectedDay, ordinary, real, cont]

theorem constructed_padding_payload (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (ordinary : i.context = 1) (padding : i.useReal = false) :
    (construct c base i).nullifier = c.hash .volumePaddingNullifier
      [base.auth.nk, base.nonce, 86400*i.dayIndex] ∧
    (construct c base i).commitment = c.hash .volumePaddingCommitment
      [base.auth.nk, base.nonce, 86400*i.dayIndex] ∧ (construct c base i).successor = 0 := by
  simp [construct, selectedDay, ordinary, padding]

-- Refusal controls compare a positively constructed semantic witness with one
-- changed field. A changed Merkle sibling requires a changed computed root;
-- no collision-resistance or hash-domain separation law is silently assumed.
theorem refuse_nullifier_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (bad : Nat) (changed : bad ≠ (construct c base i).nullifier) :
    ¬ VolumeSem c {base with volume := {construct c base i with nullifier := bad}} := by
  intro invalid
  have valid := constructed_volume_semantics c base i
  unfold VolumeSem at valid invalid
  rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,goodNF,_⟩
  rcases invalid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,badNF,_⟩
  exact changed (badNF.trans goodNF.symm)

theorem refuse_commitment_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (bad : Nat) (changed : bad ≠ (construct c base i).commitment) :
    ¬ VolumeSem c {base with volume := {construct c base i with commitment := bad}} := by
  intro invalid
  have valid := constructed_volume_semantics c base i
  unfold VolumeSem at valid invalid
  rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,goodCM⟩
  rcases invalid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,badCM⟩
  exact changed (badCM.trans goodCM.symm)

theorem refuse_day_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (bad : Nat) (changed : bad ≠ selectedDay i.toInputs) :
    ¬ VolumeSem c {base with volume := {construct c base i with dayStart := bad}} := by
  intro invalid
  unfold VolumeSem at invalid
  rcases invalid with ⟨_,_,_,_,_,_,dayEq,_⟩
  exact changed dayEq

theorem refuse_context_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (bad : Nat) (illegal : bad ≠ 1 ∧ bad ≠ 2) :
    ¬ VolumeSem c {base with volume := {construct c base i with context := bad}} := by
  intro invalid
  unfold VolumeSem at invalid
  rcases invalid with ⟨_,_,_,_,context,_⟩
  rcases context with ordinary | fee
  · exact illegal.1 ordinary
  · exact illegal.2 fee

theorem refuse_tracked_subject_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (real : i.useReal = true)
    (bad : Nat) (changed : bad ≠ selectedSubject c base) :
    ¬ VolumeSem c {base with volume := {construct c base i with subject := bad}} := by
  intro invalid
  unfold VolumeSem at invalid
  rcases invalid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,tracked,_⟩
  exact changed (tracked real).2.1

theorem refuse_continuation_head_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (real : i.useReal = true) (cont : i.startsNewDay = false)
    (bad : Nat) (changed : bad ≠ predecessor c base i.toInputs) :
    ¬ VolumeSem c {base with volume := {construct c base i with priorCommitment := bad}} := by
  intro invalid
  unfold VolumeSem at invalid
  rcases invalid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,tracked,_⟩
  have prior := (tracked real).2.2.2.2
  simp only [construct, cont, Bool.false_eq_true, ↓reduceIte] at prior
  exact changed prior.1

theorem refuse_continuation_path_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (real : i.useReal = true) (cont : i.startsNewDay = false)
    (bad : Path 24) (changed : root c .state i.priorPosition
      (predecessor c base i.toInputs) bad ≠ base.anchor) :
    ¬ VolumeSem c {base with volume := {construct c base i with priorSiblings := bad}} := by
  intro invalid
  unfold VolumeSem at invalid
  rcases invalid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,tracked,_⟩
  have prior := (tracked real).2.2.2.2
  simp only [construct, cont, Bool.false_eq_true, ↓reduceIte] at prior
  exact changed prior.2

theorem constructed_canonical_volume_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c)
    (priorBlindingCanonical : i.priorBlinding < fieldModulus)
    (successorBlindingCanonical : i.successorBlinding < fieldModulus)
    (siblingsCanonical : fieldsCanonical (pathFields i.priorSiblings)) :
    CanonicalWitness {base with volume := construct c base i} ∧
    VolumeSem c {base with volume := construct c base i} := by
  exact ⟨canonical_witness_preserved c base i baseCanonical cryptoCanonical
    priorBlindingCanonical successorBlindingCanonical siblingsCanonical,
    constructed_volume_semantics c base i⟩

/-- Domain substitution is refused when the two actual computed hash values
 differ. Domain labels alone imply no injectivity for an arbitrary Crypto. -/
theorem refuse_origin_domain_substitution (c : Crypto) (base : TransferSem.Witness)
    (i : LegalVolumeInputs c base) (real : i.useReal = true) (origin : i.startsNewDay = true)
    (wrongDomain : Domain)
    (different : c.hash wrongDomain [base.auth.nk,selectedSubject c base,86400*i.dayIndex] ≠
      c.hash .volumeOriginNullifier [base.auth.nk,selectedSubject c base,86400*i.dayIndex]) :
    ¬ VolumeSem c {base with volume := {construct c base i with
      nullifier := c.hash wrongDomain [base.auth.nk,selectedSubject c base,86400*i.dayIndex]}} := by
  apply refuse_nullifier_mutation
  rw [(constructed_origin_payload c base i real origin).1]
  exact different

#print axioms constructed_canonical_volume_semantics
#print axioms refuse_origin_domain_substitution

#print axioms fee_cannot_track
#print axioms external_requires_ordinary
#print axioms constructed_fee_payload
#print axioms constructed_origin_payload
#print axioms constructed_continuation_payload
#print axioms constructed_padding_payload
#print axioms refuse_nullifier_mutation
#print axioms refuse_commitment_mutation
#print axioms refuse_day_mutation
#print axioms refuse_context_mutation
#print axioms refuse_tracked_subject_mutation
#print axioms refuse_continuation_head_mutation
#print axioms refuse_continuation_path_mutation

#print axioms fieldsCanonical_append
#print axioms restore_full_record
#print axioms canonical_constructed_volume_fields
#print axioms canonical_witness_preserved
#print axioms constructed_volume_semantics
#print axioms nonvolume_fields_preserved
end ShielddSecurity.TransferVolumeBranchCompletion
