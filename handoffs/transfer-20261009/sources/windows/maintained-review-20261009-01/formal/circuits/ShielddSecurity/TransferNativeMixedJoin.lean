import ShielddSecurity.TransferNativeCarrierBridge
import ShielddSecurity.TransferWarmCache
import ShielddSecurity.TransferMixedExecution

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferNativeMixedJoin

open TransferAcceptance TransferAdmission TransferProjection TransferSourceBridge
open TransferFullCarrierAcceptance TransferNativeCarrierBridge

/-! Concrete model composition, not a Rust refinement. Whole native carriers
are retained through the canonical/stateless constructor. Action sources carry
all 64 independently decoded fields, complete payload identities and envelopes.
Native decoding, codecs/hash/signature arguments, source catalogue extraction,
selected-slot lookup and sibling/fee/audit/read-cache frames remain owned joins.
No local row-to-TransferSem theorem or aggregate conservation is assumed here.
The global proof interface below supplies relation witnesses, separately for
individual and batch verification. Current policies and effect readiness are
derived by executable per-operation guards at their actual model states. -/

structure NativeState where
  effects : EffectState
  policy : Environment

structure Token where
  item : Item
  contextCode : Nat

def slotCode : Slot → Nat
  | .bodyAction _ => 1
  | .feeFunding => 2

def slotIndex (bodyLength : Nat) : Slot → Nat
  | .bodyAction index => index
  | .feeFunding => bodyLength

def checkedSource (anchor : Nat) (source : SourceSlot ActionView) : SourceSlot ActionView :=
  { source with body := { source.body with contextAnchor := anchor } }

def actualItem (crypto : TransferSem.Crypto) (anchor : Nat) (source : SourceSlot ActionView) : Item :=
  sourceItem 1 (fun action => (statement action).fields) (crypto.hash .transferStatement)
    (checkedSource anchor source)

def lookup : List (Nat × Capability) → Nat → Option Capability
  | [], _ => none
  | row :: rest, index => if row.1 = index then some row.2 else lookup rest index

theorem lookup_success_member (rows : List (Nat × Capability)) (index : Nat) (capability : Capability)
    (success : lookup rows index = some capability) : (index, capability) ∈ rows := by
  induction rows with
  | nil => simp only [lookup] at success; cases success
  | cons row rest ih =>
    by_cases same : row.1 = index
    · have cap : row.2 = capability :=
        Option.some.inj (by simpa only [lookup, if_pos same] using success)
      have pair : row = (index, capability) := Prod.ext same cap
      rw [← pair]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem row (ih (by simpa only [lookup, if_neg same] using success))

def ActionCurrent (environment : Environment) (source : SourceSlot ActionView) : Prop :=
  PairGate environment ⟨source.body.decodedFields.userRoot, source.body.decodedFields.assetRoot⟩ ∧
  TimestampGate environment source.body.decodedFields.timestamp

instance (environment : Environment) (source : SourceSlot ActionView) :
    Decidable (ActionCurrent environment source) := by
  unfold ActionCurrent TimestampGate
  infer_instance

def ValidationGate {T : Type} (model : Model T ActionView) (crypto : TransferSem.Crypto)
    (registry : Nat) (carrier : TransferNativeSignaturePolicy.Carrier T)
    (slot : Slot) (source : SourceSlot ActionView) (state : NativeState) (capability : Capability) : Prop :=
  source.location = slot ∧ source.body.context.code = slotCode slot ∧
  source.body.bodyAnchor = carrier.anchor ∧ capability.registry = registry ∧
  capability.item = actualItem crypto carrier.anchor source ∧
  ActionCurrent state.policy source

instance {T : Type} (model : Model T ActionView) (crypto : TransferSem.Crypto)
    (registry : Nat) (carrier : TransferNativeSignaturePolicy.Carrier T)
    (slot : Slot) (source : SourceSlot ActionView) (state : NativeState) (capability : Capability) :
    Decidable (ValidationGate model crypto registry carrier slot source state capability) := by
  unfold ValidationGate
  infer_instance

def validate {T : Type} (model : Model T ActionView) (crypto : TransferSem.Crypto)
    (registry bodyLength : Nat) (carrier : TransferNativeSignaturePolicy.Carrier T)
    (rows : List (Nat × Capability)) (slot : Slot) (source : SourceSlot ActionView)
    (state : NativeState) : Option (NativeState × Token) :=
  match lookup rows (slotIndex bodyLength slot) with
  | none => none
  | some capability =>
      if ValidationGate model crypto registry carrier slot source state capability then
        some (state, ⟨actualItem crypto carrier.anchor source, source.body.context.code⟩)
      else none

def ExecutionGate (crypto : TransferSem.Crypto) (anchor : Nat) (slot : Slot)
    (source : SourceSlot ActionView) (token : Token) : Prop :=
  source.location = slot ∧ source.body.bodyAnchor = anchor ∧
  source.body.context.code = slotCode slot ∧ token.contextCode = source.body.context.code ∧
  token.item = actualItem crypto anchor source

instance (crypto : TransferSem.Crypto) (anchor : Nat) (slot : Slot)
    (source : SourceSlot ActionView) (token : Token) :
    Decidable (ExecutionGate crypto anchor slot source token) := by
  unfold ExecutionGate
  infer_instance

def sourceEffects (anchor : Nat) (source : SourceSlot ActionView) : TransferEffects :=
  projectEffects (project (checkedSource anchor source).body)

def execute (crypto : TransferSem.Crypto) (anchor : Nat) (slot : Slot)
    (source : SourceSlot ActionView) (token : Token) (state : NativeState) : Option NativeState :=
  if ExecutionGate crypto anchor slot source token then
    (runEffects state.effects (transferEffects (slotContext slot) (sourceEffects anchor source))).map
      (fun after => { state with effects := after })
  else none

/-- These callbacks represent separate native operations, with no assumed
preservation, rollback or conservation conclusion. Their Rust interpretation,
including complete source arguments and native error outcomes, remains open. -/
structure OtherOperations where
  putSource : NativeState → Option NativeState
  payFee : NativeState → Option NativeState
  appendAudit : NativeState → Option NativeState
  sibling : Nat → TransferMixedBody.Action (SourceSlot ActionView) → NativeState → Option NativeState
  route : Nat → TransferMixedBody.Action (SourceSlot ActionView) → NativeState → NativeState → Option NativeState

def api {T : Type} (model : Model T ActionView) (crypto : TransferSem.Crypto)
    (registry bodyLength : Nat) (carrier : TransferNativeSignaturePolicy.Carrier T)
    (rows : List (Nat × Capability)) (other : OtherOperations) :
    TransferMixedExecution.Api NativeState (SourceSlot ActionView) Token :=
  ⟨other.putSource, other.payFee, other.appendAudit,
    validate model crypto registry bodyLength carrier rows, execute crypto carrier.anchor,
    other.sibling, other.route⟩

theorem native_context_codes : Context.ordinary.code = 1 ∧ Context.feeFunding.code = 2 ∧
    slotCode (.bodyAction 0) = 1 ∧ slotCode .feeFunding = 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem validation_success {T : Type} (model : Model T ActionView) (crypto : TransferSem.Crypto)
    (registry bodyLength : Nat) (carrier : TransferNativeSignaturePolicy.Carrier T)
    (rows : List (Nat × Capability)) (slot : Slot) (source : SourceSlot ActionView)
    (state checked : NativeState) (token : Token)
    (success : validate model crypto registry bodyLength carrier rows slot source state = some (checked, token)) :
    checked = state ∧ token.item = actualItem crypto carrier.anchor source ∧
      ∃ capability, lookup rows (slotIndex bodyLength slot) = some capability ∧
        ValidationGate model crypto registry carrier slot source state capability := by
  cases found : lookup rows (slotIndex bodyLength slot) with
  | none => simp only [validate, found] at success; cases success
  | some capability =>
    by_cases gate : ValidationGate model crypto registry carrier slot source state capability
    · have same : (state, (⟨actualItem crypto carrier.anchor source, source.body.context.code⟩ : Token)) =
          (checked, token) := Option.some.inj (by simpa only [validate, found, if_pos gate] using success)
      exact ⟨(congrArg Prod.fst same).symm,
        (congrArg (fun pair : NativeState × Token => pair.2.item) same).symm, capability, rfl, gate⟩
    · simp only [validate, found, if_neg gate] at success; cases success

theorem execution_success_current_state (crypto : TransferSem.Crypto) (anchor : Nat) (slot : Slot)
    (source : SourceSlot ActionView) (token : Token) (state after : NativeState)
    (success : execute crypto anchor slot source token state = some after) :
    ExecutionGate crypto anchor slot source token ∧
    SpendReady state.effects (sourceEffects anchor source).spend0 (sourceEffects anchor source).spend1 ∧
    (slotContext slot = true → ((sourceEffects anchor source).day,
      (sourceEffects anchor source).volumeNullifier) ∉ state.effects.volumeNullifiers) ∧
    after.effects = appliedTransfer state.effects (slotContext slot) (sourceEffects anchor source) := by
  by_cases gate : ExecutionGate crypto anchor slot source token
  · cases ran : runEffects state.effects (transferEffects (slotContext slot) (sourceEffects anchor source)) with
    | none => simp only [execute, if_pos gate, ran, Option.map_none] at success; cases success
    | some result =>
      have same : ({ state with effects := result } : NativeState) = after :=
        Option.some.inj (by simpa only [execute, if_pos gate, ran, Option.map_some] using success)
      have facts := TransferExecution.successful_transfer_exact state.effects result
        (slotContext slot) (sourceEffects anchor source) ran
      exact ⟨gate, facts.1, facts.2.1, (congrArg NativeState.effects same).symm.trans facts.2.2⟩
  · simp only [execute, if_neg gate] at success; cases success

theorem constructed_signature_arguments {B : Type} (model : Model (NativeTransaction B) ActionView)
    (decode : List Nat → Option (NativeTransaction B)) (crypto : TransferSem.Crypto)
    (input : Inputs) (raw : List Nat) (entry : TransferWarmCache.Cached (NativeTransaction B))
    (made : TransferWarmCache.construct (contextModel model decode) crypto (transferInputs input) raw = some entry) :
    entry.prepared.carrier.anchor = entry.prepared.carrier.body.anchor ∧
    entry.prepared.carrier.bindingSignature = entry.prepared.carrier.body.bindingSignature ∧
    TransferNativeSignaturePolicy.bindingPolicy model.encodeBody model.authHash model.proofCount
      model.bindingKey input.verifyBinding entry.prepared.carrier ∧
    (∀ spend ∈ model.spends entry.prepared.carrier.body,
      TransferNativeSignaturePolicy.SpendBound input.verifySpend
        (model.effectHash (model.effectFields entry.prepared.carrier.body)) entry.prepared.carrier.anchor spend) := by
  have facts := TransferWarmCache.constructor_success (contextModel model decode) crypto
    (transferInputs input) raw entry made
  have carrier := native_decoder_context decode raw entry.prepared.carrier facts.2.2.1.1
  have policy := TransferNativeSignaturePolicy.full_carrier_signature_arguments
    model.encodeBody model.effectFields model.authHash model.effectHash model.proofCount model.bindingKey
    model.spends input.verifyBinding input.verifySpend entry.prepared.carrier facts.2.2.2.1.2.2.1
  exact ⟨carrier.1, carrier.2, policy.1, policy.2⟩

/-- Relation rows are derived from actual modeled verification success and the
separate global individual/batch knowledge contracts, not premised as a final
caller fact. This intentionally stops before pending local row soundness. -/
theorem constructed_compiled_claims {B F : Type} [Field F]
    (model : Model (NativeTransaction B) ActionView)
    (decode : List Nat → Option (NativeTransaction B)) (crypto : TransferSem.Crypto)
    (input : Inputs) (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop)
    (knowledge : UpstreamKnowledge (F := F) (transferInputs input) rows publicLc committed opens)
    (raw : List Nat) (entry : TransferWarmCache.Cached (NativeTransaction B))
    (made : TransferWarmCache.construct (contextModel model decode) crypto (transferInputs input) raw = some entry) :
    ∀ index ∈ (contextModel model decode).slots entry.prepared.carrier.body,
      ∃ claim, input.decodeEnvelope (expected (contextModel model decode) crypto 1 entry.prepared.carrier index).envelope =
          some claim ∧ CompiledClaim (F := F) rows publicLc committed opens
          (expected (contextModel model decode) crypto 1 entry.prepared.carrier index) claim := by
  have facts := TransferWarmCache.constructor_success (contextModel model decode) crypto
    (transferInputs input) raw entry made
  have claims := verified_compiled_claims (transferInputs input) rows publicLc committed opens knowledge
    _ _ facts.2.2.2.2.1
  intro index inside
  exact claims _ (List.mem_map.mpr ⟨index, inside, rfl⟩)

def reuseMixed {B : Type} (model : Model (NativeTransaction B) ActionView)
    (crypto : TransferSem.Crypto) (registry : Nat) (raw : List Nat)
    (entry : TransferWarmCache.Cached (NativeTransaction B))
    (bodyFromSource : B → List (TransferMixedBody.Action (SourceSlot ActionView)))
    (feeFromSource : B → Option (SourceSlot ActionView)) (other : OtherOperations) (state : NativeState) :
    Option (TransferMixedExecution.Outcome NativeState (SourceSlot ActionView) Token) :=
  if entry.registry = registry ∧ entry.raw = raw ∧ entry.prepared.carrier.anchor ∈ state.policy.noteRoots then
    let body := bodyFromSource entry.prepared.carrier.body.body
    TransferMixedExecution.run
      (api model crypto registry body.length entry.prepared.carrier entry.prepared.rows other)
      body (feeFromSource entry.prepared.carrier.body.body) state
  else none

theorem warm_mixed_success_checks {B : Type} (model : Model (NativeTransaction B) ActionView)
    (crypto : TransferSem.Crypto) (registry : Nat) (raw : List Nat)
    (entry : TransferWarmCache.Cached (NativeTransaction B))
    (bodyFromSource : B → List (TransferMixedBody.Action (SourceSlot ActionView)))
    (feeFromSource : B → Option (SourceSlot ActionView)) (other : OtherOperations) (state : NativeState)
    (result : TransferMixedExecution.Outcome NativeState (SourceSlot ActionView) Token)
    (success : reuseMixed model crypto registry raw entry bodyFromSource feeFromSource other state = some result) :
    entry.registry = registry ∧ entry.raw = raw ∧ entry.prepared.carrier.anchor ∈ state.policy.noteRoots ∧
    TransferMixedExecution.Checks
      (api model crypto registry (bodyFromSource entry.prepared.carrier.body.body).length
        entry.prepared.carrier entry.prepared.rows other)
      (bodyFromSource entry.prepared.carrier.body.body)
      (feeFromSource entry.prepared.carrier.body.body) state result := by
  by_cases hit : entry.registry = registry ∧ entry.raw = raw ∧
      entry.prepared.carrier.anchor ∈ state.policy.noteRoots
  · have ran : TransferMixedExecution.run
        (api model crypto registry (bodyFromSource entry.prepared.carrier.body.body).length
          entry.prepared.carrier entry.prepared.rows other)
        (bodyFromSource entry.prepared.carrier.body.body) (feeFromSource entry.prepared.carrier.body.body) state =
          some result := by simpa only [reuseMixed, if_pos hit] using success
    exact ⟨hit.1, hit.2.1, hit.2.2, TransferMixedExecution.run_success_checks _ _ _ _ _ ran⟩
  · simp only [reuseMixed, if_neg hit] at success; cases success

/-- All local admission/effect facts are obtained at the actual per-step states.
The exact native source Item matches a constructor-attached proof occurrence;
the global relation witness is then derived from that verification. No final
current-time/NF, supplied rows or desired Transfer semantics is a premise. -/
theorem mixed_transfer_native_consequence {B F : Type} [Field F]
    (model : Model (NativeTransaction B) ActionView)
    (decode : List Nat → Option (NativeTransaction B)) (crypto : TransferSem.Crypto)
    (input : Inputs) (rows : List Row) (publicLc committed : Linear) (opens : List Nat → Nat → Prop)
    (knowledge : UpstreamKnowledge (F := F) (transferInputs input) rows publicLc committed opens)
    (constructedRaw raw : List Nat) (entry : TransferWarmCache.Cached (NativeTransaction B))
    (bodyFromSource : B → List (TransferMixedBody.Action (SourceSlot ActionView)))
    (feeFromSource : B → Option (SourceSlot ActionView)) (other : OtherOperations) (state : NativeState)
    (result : TransferMixedExecution.Outcome NativeState (SourceSlot ActionView) Token)
    (made : TransferWarmCache.construct (contextModel model decode) crypto (transferInputs input) constructedRaw = some entry)
    (success : reuseMixed (contextModel model decode) crypto input.registry.identity raw entry
      bodyFromSource feeFromSource other state = some result) :
    ∀ step ∈ result.steps, step.action.kind = .transfer →
      ActionCurrent step.before.policy step.action.source ∧
      SpendReady step.checked.effects (sourceEffects entry.prepared.carrier.anchor step.action.source).spend0
        (sourceEffects entry.prepared.carrier.anchor step.action.source).spend1 ∧
      ((sourceEffects entry.prepared.carrier.anchor step.action.source).day,
        (sourceEffects entry.prepared.carrier.anchor step.action.source).volumeNullifier) ∉
          step.checked.effects.volumeNullifiers ∧
      ∃ claim, input.decodeEnvelope (actualItem crypto entry.prepared.carrier.anchor step.action.source).envelope =
          some claim ∧ CompiledClaim (F := F) rows publicLc committed opens
          (actualItem crypto entry.prepared.carrier.anchor step.action.source) claim := by
  have madeFacts := TransferWarmCache.constructor_success (contextModel model decode) crypto
    (transferInputs input) constructedRaw entry made
  have bound := attachment_derives_bound_rows input.registry.identity
    (expected (contextModel model decode) crypto 1 entry.prepared.carrier)
    ((contextModel model decode).slots entry.prepared.carrier.body) entry.prepared.capabilities entry.prepared.rows
    madeFacts.2.2.2.2.2
  have claims := constructed_compiled_claims model decode crypto input rows publicLc committed opens
    knowledge constructedRaw entry made
  have checks := (warm_mixed_success_checks (contextModel model decode) crypto input.registry.identity raw
    entry bodyFromSource feeFromSource other state result success).2.2.2
  have operations := TransferMixedExecution.trace_each_operation
    (api (contextModel model decode) crypto input.registry.identity
      (bodyFromSource entry.prepared.carrier.body.body).length entry.prepared.carrier entry.prepared.rows other)
    checks.2.2.2.2.1
  intro step inside kind
  rcases (operations step inside).1 with native | sibling
  · obtain ⟨_, token, _, validated, executed⟩ := native
    have validation := validation_success (contextModel model decode) crypto input.registry.identity
      (bodyFromSource entry.prepared.carrier.body.body).length entry.prepared.carrier entry.prepared.rows
      (.bodyAction step.index) step.action.source step.before step.checked token validated
    obtain ⟨capability, found, gate⟩ := validation.2.2
    have member : (step.index, capability) ∈ entry.prepared.rows := lookup_success_member _ _ _ found
    have boundItem := (bound.binds (step.index, capability) member).2
    have itemSame : actualItem crypto entry.prepared.carrier.anchor step.action.source =
        expected (contextModel model decode) crypto 1 entry.prepared.carrier step.index :=
      gate.2.2.2.2.1.symm.trans boundItem
    have selected : step.index ∈ (contextModel model decode).slots entry.prepared.carrier.body :=
      bound.exactCoverage.mem_iff.mp (List.mem_map.mpr ⟨(step.index, capability), member, rfl⟩)
    have compiled := claims step.index selected
    have effects := execution_success_current_state crypto entry.prepared.carrier.anchor
      (.bodyAction step.index) step.action.source token step.checked step.executed executed
    refine ⟨gate.2.2.2.2.2, effects.2.1, effects.2.2.1 rfl, ?_⟩
    simpa only [itemSame] using compiled
  · exact False.elim (sibling.1 kind)

/-- The funding policy is checked before the body; its token executes against
the actual post-body effects. This does not transport pre-body NF freshness or
assert that an arbitrary routing callback preserves the execution state. -/
theorem funding_native_consequence {B : Type}
    (model : Model (NativeTransaction B) ActionView) (crypto : TransferSem.Crypto)
    (registry : Nat) (raw : List Nat) (entry : TransferWarmCache.Cached (NativeTransaction B))
    (bodyFromSource : B → List (TransferMixedBody.Action (SourceSlot ActionView)))
    (feeFromSource : B → Option (SourceSlot ActionView)) (other : OtherOperations)
    (state : NativeState) (result : TransferMixedExecution.Outcome NativeState (SourceSlot ActionView) Token)
    (fee : SourceSlot ActionView) (hasFee : feeFromSource entry.prepared.carrier.body.body = some fee)
    (success : reuseMixed model crypto registry raw entry bodyFromSource feeFromSource other state = some result) :
    fee.body.context.code = 2 ∧ ActionCurrent result.audited.policy fee ∧
      ∃ executed, SpendReady result.bodyAfter.effects
        (sourceEffects entry.prepared.carrier.anchor fee).spend0
        (sourceEffects entry.prepared.carrier.anchor fee).spend1 ∧
        executed.effects = appliedTransfer result.bodyAfter.effects false
          (sourceEffects entry.prepared.carrier.anchor fee) ∧
        other.route (bodyFromSource entry.prepared.carrier.body.body).length
          ⟨.transfer, fee⟩ result.bodyAfter executed = some result.after := by
  let operations := api model crypto registry (bodyFromSource entry.prepared.carrier.body.body).length
    entry.prepared.carrier entry.prepared.rows other
  have checks := (warm_mixed_success_checks model crypto registry raw entry bodyFromSource feeFromSource
    other state result success).2.2.2
  have fundingCheck := checks.2.2.2.1
  rw [hasFee] at fundingCheck
  obtain ⟨token, retained, validated⟩ := TransferMixedExecution.funding_validation_source
    operations fee result.audited result.preBody result.retainedFunding fundingCheck
  have funded := checks.2.2.2.2.2
  rw [retained] at funded
  obtain ⟨executed, applied, routed⟩ := TransferMixedExecution.funding_execution_retains_token
    operations (bodyFromSource entry.prepared.carrier.body.body).length fee token
    result.bodyAfter result.after funded
  have validation := validation_success model crypto registry
    (bodyFromSource entry.prepared.carrier.body.body).length entry.prepared.carrier entry.prepared.rows
    .feeFunding fee result.audited result.preBody token validated
  obtain ⟨capability, _, gate⟩ := validation.2.2
  have execution := execution_success_current_state crypto entry.prepared.carrier.anchor
    .feeFunding fee token result.bodyAfter executed applied
  exact ⟨gate.2.1, gate.2.2.2.2.2, executed, execution.2.1, execution.2.2.2, routed⟩

set_option pp.all true in
#check @native_context_codes
#print axioms native_context_codes
set_option pp.all true in
#check @validation_success
#print axioms validation_success
set_option pp.all true in
#check @execution_success_current_state
#print axioms execution_success_current_state
set_option pp.all true in
#check @constructed_signature_arguments
#print axioms constructed_signature_arguments
set_option pp.all true in
#check @constructed_compiled_claims
#print axioms constructed_compiled_claims
set_option pp.all true in
#check @warm_mixed_success_checks
#print axioms warm_mixed_success_checks
set_option pp.all true in
#check @lookup_success_member
#print axioms lookup_success_member
set_option pp.all true in
#check @mixed_transfer_native_consequence
#print axioms mixed_transfer_native_consequence
set_option pp.all true in
#check @funding_native_consequence
#print axioms funding_native_consequence

end ShielddSecurity.TransferNativeMixedJoin
