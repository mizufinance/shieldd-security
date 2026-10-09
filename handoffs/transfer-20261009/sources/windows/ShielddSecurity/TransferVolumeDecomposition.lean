import ShielddSecurity.TransferVolumeBranchCompletion

set_option maxHeartbeats 250000

/-! Recover legal raw volume inputs and preserve public volume fields. Inactive
subject, predecessor and successor auxiliaries need not equal the constructor's
normalized storage. The inverse result therefore establishes exact observable
fields rather than claiming equality of every private auxiliary. -/
namespace ShielddSecurity.TransferVolumeDecomposition

open TransferCore TransferSem TransferVolumeBranchCompletion

def recoverRaw (w : TransferSem.Witness) : Inputs :=
  {context := w.volume.context, useReal := w.volume.useReal,
    startsNewDay := w.volume.startsNewDay, dayIndex := w.volume.dayIndex,
    second := w.volume.second, prior := w.volume.prior,
    priorBlinding := w.volume.priorBlinding, priorPosition := w.volume.priorPosition,
    priorSiblings := w.volume.priorSiblings, successorBlinding := w.volume.successorBlinding}

theorem selected_day_recovered (c : Crypto) (w : TransferSem.Witness)
    (legal : VolumeSem c w) : selectedDay (recoverRaw w) = w.volume.dayStart :=
  legal.2.2.2.2.2.2.1.symm

def recoverInputs (c : Crypto) (w : TransferSem.Witness) (legal : VolumeSem c w)
    (outboundPositive : 0 < (w.outputs 0).amount)
    (outboundBound : (w.outputs 0).amount < amountBound) : LegalVolumeInputs c w where
  toInputs := recoverRaw w
  timestampBound := legal.1
  dayBound := legal.2.1
  secondBound := legal.2.2.1
  timeSplit := legal.2.2.2.1
  contextValid := legal.2.2.2.2.1
  feeSelf := legal.2.2.2.2.2.1
  priorBound := legal.2.2.2.2.2.2.2.1
  outboundPositive := outboundPositive
  outboundBound := outboundBound
  candidateBound := legal.2.2.2.2.2.2.2.2.2.2.1
  limitBound := legal.2.2.2.2.2.2.2.2.2.1
  positionBound := legal.2.2.2.2.2.2.2.2.2.2.2.1
  trackedEligible := by
    have tracked := legal.2.2.2.2.2.2.2.2.2.2.2.2.1
    intro enabled
    have eligible := (tracked enabled).1
    simp only [TransferSem.eligible, Bool.and_eq_true, decide_eq_true_eq] at eligible
    exact ⟨eligible.1.1, eligible.1.2, eligible.2⟩
  trackedLimit := by
    have tracked := legal.2.2.2.2.2.2.2.2.2.2.2.2.1
    intro enabled
    have successor := (tracked enabled).2.2.1
    have bound := (tracked enabled).2.2.2.1
    rw [successor] at bound
    exact bound
  originZero := by
    have tracked := legal.2.2.2.2.2.2.2.2.2.2.2.2.1
    intro enabled origin
    change w.volume.startsNewDay = true at origin
    have branch := (tracked enabled).2.2.2.2
    rw [if_pos origin] at branch
    exact branch
  continuationAuthenticated := by
    have tracked := legal.2.2.2.2.2.2.2.2.2.2.2.2.1
    have dayEquation := legal.2.2.2.2.2.2.1
    intro enabled continuation
    change w.volume.startsNewDay = false at continuation
    have subject := (tracked enabled).2.1
    have branch := (tracked enabled).2.2.2.2
    rw [if_neg (by simp only [continuation, Bool.false_eq_true, not_false_eq_true])] at branch
    change root c .state w.volume.priorPosition
      (volumeState c (c.hash .volumeSubject (addressFields w.sender.address ++ [w.asset]))
        (if w.volume.context = 1 then 86400 * w.volume.dayIndex else 0)
        w.volume.prior w.volume.priorBlinding) w.volume.priorSiblings = w.anchor
    rw [← subject, ← dayEquation]
    exact branch.2

theorem recovered_raw_inputs (c : Crypto) (w : TransferSem.Witness) (legal : VolumeSem c w)
    (positive : 0 < (w.outputs 0).amount) (bounded : (w.outputs 0).amount < amountBound) :
    (recoverInputs c w legal positive bounded).toInputs = recoverRaw w := by
  rfl

theorem constructed_public_volume (c : Crypto) (w : TransferSem.Witness) (legal : VolumeSem c w)
    (positive : 0 < (w.outputs 0).amount) (bounded : (w.outputs 0).amount < amountBound) :
    let volume := construct c w (recoverInputs c w legal positive bounded)
    volume.nullifier = w.volume.nullifier ∧ volume.commitment = w.volume.commitment ∧
      volume.dayStart = w.volume.dayStart ∧ volume.context = w.volume.context := by
  rcases legal with ⟨_, _, _, _, _, _, dayEquation, _, _, _, _, _, tracked, nullifier, commitment⟩
  change
    (if w.volume.context = 2 then 0 else if w.volume.useReal then
      (if w.volume.startsNewDay then c.hash .volumeOriginNullifier
        [w.auth.nk, selectedSubject c w, selectedDay (recoverRaw w)]
       else c.hash .noteNullifier [w.auth.nk, predecessor c w (recoverRaw w), w.volume.priorPosition])
      else c.hash .volumePaddingNullifier [w.auth.nk, w.nonce, selectedDay (recoverRaw w)]) =
      w.volume.nullifier ∧
    (if w.volume.context = 2 then 0 else if w.volume.useReal then
      volumeState c (selectedSubject c w) (selectedDay (recoverRaw w))
        (if w.volume.useReal then w.volume.prior + (w.outputs 0).amount else 0)
        w.volume.successorBlinding
      else c.hash .volumePaddingCommitment [w.auth.nk, w.nonce, selectedDay (recoverRaw w)]) =
      w.volume.commitment ∧
    selectedDay (recoverRaw w) = w.volume.dayStart ∧ w.volume.context = w.volume.context
  have day : selectedDay (recoverRaw w) = w.volume.dayStart := dayEquation.symm
  unfold predecessor
  rw [day]
  cases selected : w.volume.useReal with
  | false =>
    simp only [selected, Bool.false_eq_true, if_false] at nullifier commitment ⊢
    exact ⟨nullifier.symm, commitment.symm, trivial, trivial⟩
  | true =>
    have subject := (tracked selected).2.1
    have successor := (tracked selected).2.2.1
    change w.volume.subject = selectedSubject c w at subject
    simp only [selected, if_true] at nullifier commitment ⊢
    rw [← subject, ← successor]
    exact ⟨nullifier.symm, commitment.symm, trivial, trivial⟩

theorem full_public_statement_preserved (c : Crypto) (w : TransferSem.Witness)
    (legal : VolumeSem c w) (positive : 0 < (w.outputs 0).amount)
    (bounded : (w.outputs 0).amount < amountBound) :
    publicFields c {w with volume := construct c w (recoverInputs c w legal positive bounded)} =
      publicFields c w := by
  have fields := constructed_public_volume c w legal positive bounded
  unfold publicFields
  dsimp only
  rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2]
  rfl

theorem relation_inputs_preserved (c : Crypto) (w : TransferSem.Witness)
    (legal : VolumeSem c w) (positive : 0 < (w.outputs 0).amount)
    (bounded : (w.outputs 0).amount < amountBound) :
    let normalized := {w with volume := construct c w (recoverInputs c w legal positive bounded)}
    c.hash .transferStatement (publicFields c normalized) =
      c.hash .transferStatement (publicFields c w) ∧ normalized.blinding = w.blinding :=
  ⟨congrArg (c.hash .transferStatement)
    (full_public_statement_preserved c w legal positive bounded), rfl⟩

set_option pp.all true in
#check @selected_day_recovered
#print axioms selected_day_recovered
set_option pp.all true in
#check @recovered_raw_inputs
#print axioms recovered_raw_inputs
set_option pp.all true in
#check @constructed_public_volume
#print axioms constructed_public_volume
set_option pp.all true in
#check @full_public_statement_preserved
#print axioms full_public_statement_preserved
set_option pp.all true in
#check @relation_inputs_preserved
#print axioms relation_inputs_preserved

end ShielddSecurity.TransferVolumeDecomposition
