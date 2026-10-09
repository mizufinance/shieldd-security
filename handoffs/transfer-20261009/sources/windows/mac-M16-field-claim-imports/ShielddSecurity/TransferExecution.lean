import ShielddSecurity.TransferAcceptance
import ShielddSecurity.TransferAdmission

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferExecution

open TransferAdmission TransferAcceptance

/-!
Successful execution consequences for the existing unbounded effect model.
The readiness and exact poststate are derived from its executable program,
not supplied as opaque conservation/effect premises. Identifiers are already
decoded values. Rust field projection, source/codec/hash correspondence, SCT
error behavior and participating-store durability remain separate joins.
-/

theorem success_requires_spend_ready (state after : EffectState)
    (ordinary : Bool) (effects : TransferEffects)
    (success : runEffects state (transferEffects ordinary effects) = some after) :
    SpendReady state effects.spend0 effects.spend1 := by
  by_cases ready : SpendReady state effects.spend0 effects.spend1
  · exact ready
  · cases ordinary <;>
      simp [runEffects, transferEffects, effectStep, ready] at success

theorem ordinary_success_requires_volume_fresh (state after : EffectState)
    (effects : TransferEffects)
    (success : runEffects state (transferEffects true effects) = some after) :
    (effects.day, effects.volumeNullifier) ∉ state.volumeNullifiers := by
  have ready := success_requires_spend_ready state after true effects success
  intro spent
  simp [runEffects, transferEffects, effectStep, ready, spent] at success

theorem successful_transfer_exact (state after : EffectState)
    (ordinary : Bool) (effects : TransferEffects)
    (success : runEffects state (transferEffects ordinary effects) = some after) :
    SpendReady state effects.spend0 effects.spend1 ∧
    (ordinary = true → (effects.day, effects.volumeNullifier) ∉ state.volumeNullifiers) ∧
    after = appliedTransfer state ordinary effects := by
  have ready := success_requires_spend_ready state after ordinary effects success
  have fresh : ordinary = true → (effects.day, effects.volumeNullifier) ∉ state.volumeNullifiers := by
    intro isOrdinary
    subst ordinary
    exact ordinary_success_requires_volume_fresh state after effects success
  have exactResult := exact_transfer_effects state ordinary effects ready fresh
  rw [exactResult] at success
  exact ⟨ready, fresh, (Option.some.inj success).symm⟩

theorem successful_slots_and_outputs (state after : EffectState)
    (ordinary : Bool) (effects : TransferEffects)
    (success : runEffects state (transferEffects ordinary effects) = some after) :
    after.pendingNullifiers = state.pendingNullifiers ++ [effects.spend0, effects.spend1] ∧
    after.notes = state.notes ++ [effects.output0, effects.output1] := by
  have same := (successful_transfer_exact state after ordinary effects success).2.2
  rw [same]
  exact ⟨rfl, rfl⟩

theorem successful_fee_has_no_volume (state after : EffectState) (fee : TransferEffects)
    (success : runEffects state (transferEffects false fee) = some after) :
    after.volumeNullifiers = state.volumeNullifiers ∧
    after.volumePayloads = state.volumePayloads := by
  have same := (successful_transfer_exact state after false fee success).2.2
  rw [same]
  exact fee_funding_no_volume_effects state fee

/-- Extract a successful prefix from an arbitrary unbounded suffix. -/
theorem successful_prefix (state after : EffectState) (earlierCommands suffix : List EffectCommand)
    (success : runEffects state (earlierCommands ++ suffix) = some after) :
    ∃ middle, runEffects state earlierCommands = some middle ∧ runEffects middle suffix = some after := by
  rw [run_effects_append] at success
  cases result : runEffects state earlierCommands with
  | none => simp [result] at success
  | some middle =>
      exact ⟨middle, rfl, by simpa [result] using success⟩

/-- Execution checks the current day/nullifier collection. A token validated
against an earlier state cannot make a repeated Ordinary volume slot succeed.
This model result does not recheck native paired roots or timestamp policy. -/
theorem ordinary_current_volume_conflict_rejects (state : EffectState)
    (effects : TransferEffects)
    (spent : (effects.day, effects.volumeNullifier) ∈ state.volumeNullifiers) :
    ¬ ∃ after, runEffects state (transferEffects true effects) = some after := by
  rintro ⟨after, success⟩
  exact ordinary_success_requires_volume_fresh state after effects success spent

/-- Funding effects preserve volume after the entire preceding program.
The preserved state is the actual successful intermediate state, so an earlier
body volume update is retained rather than replaced by a validation snapshot. -/
theorem successful_fee_after_prefix_preserves_current_volume
    (state after : EffectState) (earlierCommands : List EffectCommand)
    (fee : TransferEffects)
    (success : runEffects state (earlierCommands ++ transferEffects false fee) = some after) :
    ∃ middle, runEffects state earlierCommands = some middle ∧
      after.volumeNullifiers = middle.volumeNullifiers ∧
      after.volumePayloads = middle.volumePayloads := by
  obtain ⟨middle, earlierSuccess, feeSuccess⟩ :=
    successful_prefix state after earlierCommands (transferEffects false fee) success
  have preserved := successful_fee_has_no_volume middle after fee feeSuccess
  exact ⟨middle, earlierSuccess, preserved.1, preserved.2⟩

theorem successful_body_and_fee_exact (state after : EffectState)
    (body fee : TransferEffects)
    (success : runEffects state (bodyAndFeeEffects (transferEffects true body) (some fee)) = some after) :
    SpendReady state body.spend0 body.spend1 ∧
    (body.day, body.volumeNullifier) ∉ state.volumeNullifiers ∧
    SpendReady (appliedTransfer state true body) fee.spend0 fee.spend1 ∧
    after = appliedTransfer (appliedTransfer state true body) false fee := by
  have decomposition :
      runEffects state (transferEffects true body ++ transferEffects false fee) = some after := success
  obtain ⟨middle, bodySuccess, feeSuccess⟩ :=
    successful_prefix state after _ _ decomposition
  obtain ⟨bodyReady, bodyFresh, bodyExact⟩ := successful_transfer_exact state middle true body bodySuccess
  rw [bodyExact] at feeSuccess
  obtain ⟨feeReady, _, feeExact⟩ := successful_transfer_exact _ after false fee feeSuccess
  exact ⟨bodyReady, bodyFresh rfl, feeReady, feeExact⟩

/-- Membership in the earlier body slots precludes success of either fee slot.
This is a consequence of sequential execution, independently of proof legality. -/
theorem body_fee_slot_conflict_rejects (state : EffectState) (body fee : TransferEffects)
    (conflict : fee.spend0 = body.spend0) :
    ¬ ∃ after, runEffects state (bodyAndFeeEffects (transferEffects true body) (some fee)) = some after := by
  rintro ⟨after, success⟩
  have feeReady := (successful_body_and_fee_exact state after body fee success).2.2.1
  have fresh := feeReady.2.1
  apply fresh
  simp [appliedTransfer, conflict]

/-- Application composition only: the verified semantic contract is explicitly
upstream/conditional and still requires correctly generated matching keys and
the full Transfer row-to-semantic join. Exact slot coverage is the existing
checked application precondition. Model success derives effect readiness and
poststate; no Rust refinement, hash injectivity or opaque no-inflation follows. -/
theorem accepted_slot_and_successful_effects
    (slots : List Nat) (expected : Nat → Item) (rows : List (Nat × Capability))
    (registry slot : Nat) (contract : Item → Prop)
    (bound : BoundRows slots expected rows registry) (inside : slot ∈ slots)
    (verifiedContract : ∀ row ∈ rows, row.2.registry = registry → contract row.2.item)
    (effectProjection : Item → TransferEffects)
    (state after : EffectState) (ordinary : Bool)
    (success : runEffects state (transferEffects ordinary (effectProjection (expected slot))) = some after) :
    contract (expected slot) ∧
    SpendReady state (effectProjection (expected slot)).spend0 (effectProjection (expected slot)).spend1 ∧
    after = appliedTransfer state ordinary (effectProjection (expected slot)) := by
  have semantic := expected_slots_satisfy_contract slots expected rows registry contract bound verifiedContract slot inside
  obtain ⟨ready, _, exactEffects⟩ := successful_transfer_exact state after ordinary (effectProjection (expected slot)) success
  exact ⟨semantic, ready, exactEffects⟩

set_option pp.all true in
#check @success_requires_spend_ready
#print axioms success_requires_spend_ready
set_option pp.all true in
#check @ordinary_success_requires_volume_fresh
#print axioms ordinary_success_requires_volume_fresh
set_option pp.all true in
#check @successful_transfer_exact
#print axioms successful_transfer_exact
set_option pp.all true in
#check @successful_slots_and_outputs
#print axioms successful_slots_and_outputs
set_option pp.all true in
#check @successful_fee_has_no_volume
#print axioms successful_fee_has_no_volume
set_option pp.all true in
#check @successful_prefix
#print axioms successful_prefix
set_option pp.all true in
#check @successful_body_and_fee_exact
#print axioms successful_body_and_fee_exact
set_option pp.all true in
#check @body_fee_slot_conflict_rejects
#print axioms body_fee_slot_conflict_rejects
set_option pp.all true in
#check @accepted_slot_and_successful_effects
#print axioms accepted_slot_and_successful_effects

set_option pp.all true in
#check @ordinary_current_volume_conflict_rejects
#print axioms ordinary_current_volume_conflict_rejects
set_option pp.all true in
#check @successful_fee_after_prefix_preserves_current_volume
#print axioms successful_fee_after_prefix_preserves_current_volume

end ShielddSecurity.TransferExecution
