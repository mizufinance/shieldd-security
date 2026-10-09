import ShielddSecurity.TransferExecution

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferProjection

open TransferAdmission TransferAcceptance TransferExecution

/-!
Independent typed projection of a retained native Transfer action. A proof Item
contains a statement hash and envelope, so it cannot be used to recover complete
payloads. Payload Nat values identify complete decoded native payloads, distinct
from their commitment fields. Native decoding/serialization and the full64-field
statement/hash interpretation are explicit source contracts, not established by
these projection lemmas. This model covers Transfer-only body actions and fee.
-/

structure NativeOutput where
  noteCommitment : Nat
  payload : Nat

structure NativeVolume where
  day : Nat
  nullifier : Nat
  commitment : Nat
  payload : Nat

structure NativeBody where
  spend0 : Nat
  spend1 : Nat
  output0 : NativeOutput
  output1 : NativeOutput
  volume : NativeVolume
  ordinaryContext : Bool

def projectEffects (body : NativeBody) : TransferEffects :=
  { spend0 := body.spend0, spend1 := body.spend1
    output0 := body.output0.payload, output1 := body.output1.payload
    day := body.volume.day, volumeNullifier := body.volume.nullifier
    volumePayload := body.volume.payload }

structure RetainedAction where
  body : NativeBody
  item : Item

/-- The full canonical field projection is supplied separately; hashing never
inverts the native action. The same retained body supplies effects and Item. -/
def retainAction (family : Nat) (fields : NativeBody → List Nat)
    (hash : List Nat → Nat) (envelope : List Nat) (body : NativeBody) : RetainedAction :=
  ⟨body, ⟨family, hash (fields body), envelope⟩⟩

inductive Slot where
  | bodyAction (index : Nat)
  | feeFunding
  deriving DecidableEq

def slotContext : Slot → Bool
  | .bodyAction _ => true
  | .feeFunding => false

def slotEffects (slot : Slot) (body : NativeBody) : Option (List EffectCommand) :=
  if body.ordinaryContext = slotContext slot then
    some (transferEffects (slotContext slot) (projectEffects body))
  else none

def bodySlotsFrom (index : Nat) : List NativeBody → List (Slot × NativeBody)
  | [] => []
  | body :: rest => (.bodyAction index, body) :: bodySlotsFrom (index + 1) rest

def nativeSlots (bodies : List NativeBody) (fee : Option NativeBody) : List (Slot × NativeBody) :=
  bodySlotsFrom 0 bodies ++ match fee with
    | none => []
    | some body => [(.feeFunding, body)]

theorem retained_body_exact (family : Nat) (fields : NativeBody → List Nat)
    (hash : List Nat → Nat) (envelope : List Nat) (body : NativeBody) :
    (retainAction family fields hash envelope body).body = body := by rfl

theorem retained_item_derived (family : Nat) (fields : NativeBody → List Nat)
    (hash : List Nat → Nat) (envelope : List Nat) (body : NativeBody) :
    (retainAction family fields hash envelope body).item = ⟨family, hash (fields body), envelope⟩ := by rfl

theorem projection_preserves_both_slots (body : NativeBody) :
    (projectEffects body).spend0 = body.spend0 ∧
    (projectEffects body).spend1 = body.spend1 ∧
    (projectEffects body).output0 = body.output0.payload ∧
    (projectEffects body).output1 = body.output1.payload := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem projection_preserves_volume (body : NativeBody) :
    (projectEffects body).day = body.volume.day ∧
    (projectEffects body).volumeNullifier = body.volume.nullifier ∧
    (projectEffects body).volumePayload = body.volume.payload := by
  exact ⟨rfl, rfl, rfl⟩

theorem body_slots_length (index : Nat) (bodies : List NativeBody) :
    (bodySlotsFrom index bodies).length = bodies.length := by
  induction bodies generalizing index with
  | nil => rfl
  | cons body rest ih => simp [bodySlotsFrom, ih]

theorem body_slot_order (index : Nat) (body : NativeBody) (rest : List NativeBody) :
    bodySlotsFrom index (body :: rest) =
      (.bodyAction index, body) :: bodySlotsFrom (index + 1) rest := by rfl

theorem fee_slot_after_body (bodies : List NativeBody) (fee : NativeBody) :
    nativeSlots bodies (some fee) = bodySlotsFrom 0 bodies ++ [(.feeFunding, fee)] := by rfl

theorem native_slot_count (bodies : List NativeBody) (fee : Option NativeBody) :
    (nativeSlots bodies fee).length = bodies.length + (if fee.isSome then 1 else 0) := by
  cases fee <;> simp [nativeSlots, body_slots_length]

theorem duplicate_body_occurrences_preserved (index : Nat) (body : NativeBody) :
    bodySlotsFrom index [body, body] =
      [(.bodyAction index, body), (.bodyAction (index + 1), body)] := by rfl

theorem wrong_slot_context_refused (slot : Slot) (body : NativeBody)
    (wrong : body.ordinaryContext ≠ slotContext slot) : slotEffects slot body = none := by
  simp [slotEffects, wrong]

theorem fee_slot_has_only_fixed_spends_outputs (body : NativeBody)
    (context : body.ordinaryContext = false) :
    slotEffects .feeFunding body = some
      [.spend body.spend0 body.spend1, .note body.output0.payload, .note body.output1.payload] := by
  simp [slotEffects, slotContext, context, transferEffects, projectEffects]

/-- A semantic contract on the same retained Item and a successful projected
program yield semantics plus exact effects. The contract is conditional on the
upstream correct-key/knowledge and complete Transfer row refinement. This does
not certify native Rust execution or infer full payload validity from a digest. -/
theorem retained_action_success_consequence (family : Nat) (fields : NativeBody → List Nat)
    (hash : List Nat → Nat) (envelope : List Nat) (body : NativeBody)
    (contract : Item → Prop)
    (verified : contract (retainAction family fields hash envelope body).item)
    (state after : EffectState) (slot : Slot)
    (success : (slotEffects slot (retainAction family fields hash envelope body).body).bind
      (fun commands => runEffects state commands) = some after) :
    contract ⟨family, hash (fields body), envelope⟩ ∧
    body.ordinaryContext = slotContext slot ∧
    SpendReady state body.spend0 body.spend1 ∧
    after = appliedTransfer state (slotContext slot) (projectEffects body) := by
  by_cases context : body.ordinaryContext = slotContext slot
  · have execution : runEffects state (transferEffects (slotContext slot) (projectEffects body)) = some after := by
      simpa [slotEffects, retainAction, context] using success
    obtain ⟨ready, _, effects⟩ := successful_transfer_exact state after (slotContext slot) (projectEffects body) execution
    exact ⟨verified, context, ready, effects⟩
  · simp [slotEffects, retainAction, context] at success

/-- Compose actual capability-slot coverage with the independently retained
native action model. The expected Item and executable effects are constructed
from the same indexed native body; no arbitrary Item-to-payload recovery or
supplied equality between two unrelated effects projections is required.
`verifiedContract` remains the explicit upstream/full-row semantic boundary.
Rust slot enumeration, codecs, fields/hash correspondence and execution are not
proved by this symbolic application composition. -/
theorem admitted_retained_slot_success (family : Nat) (fields : NativeBody → List Nat)
    (hash : List Nat → Nat) (envelopes : Nat → List Nat) (bodies : Nat → NativeBody)
    (slots : List Nat) (rows : List (Nat × Capability)) (registry slot : Nat)
    (contract : Item → Prop)
    (bound : BoundRows slots
      (fun index => (retainAction family fields hash (envelopes index) (bodies index)).item)
      rows registry)
    (inside : slot ∈ slots)
    (verifiedContract : ∀ row ∈ rows, row.2.registry = registry → contract row.2.item)
    (state after : EffectState) (location : Slot)
    (success : (slotEffects location (bodies slot)).bind
      (fun commands => runEffects state commands) = some after) :
    contract (retainAction family fields hash (envelopes slot) (bodies slot)).item ∧
    (bodies slot).ordinaryContext = slotContext location ∧
    SpendReady state (bodies slot).spend0 (bodies slot).spend1 ∧
    after = appliedTransfer state (slotContext location) (projectEffects (bodies slot)) := by
  have semantic := expected_slots_satisfy_contract slots
    (fun index => (retainAction family fields hash (envelopes index) (bodies index)).item)
    rows registry contract bound verifiedContract slot inside
  exact retained_action_success_consequence family fields hash (envelopes slot) (bodies slot)
    contract semantic state after location success

set_option pp.all true in
#check @retained_body_exact
#print axioms retained_body_exact
set_option pp.all true in
#check @retained_item_derived
#print axioms retained_item_derived
set_option pp.all true in
#check @projection_preserves_both_slots
#print axioms projection_preserves_both_slots
set_option pp.all true in
#check @projection_preserves_volume
#print axioms projection_preserves_volume
set_option pp.all true in
#check @body_slots_length
#print axioms body_slots_length
set_option pp.all true in
#check @body_slot_order
#print axioms body_slot_order
set_option pp.all true in
#check @fee_slot_after_body
#print axioms fee_slot_after_body
set_option pp.all true in
#check @native_slot_count
#print axioms native_slot_count
set_option pp.all true in
#check @duplicate_body_occurrences_preserved
#print axioms duplicate_body_occurrences_preserved
set_option pp.all true in
#check @wrong_slot_context_refused
#print axioms wrong_slot_context_refused
set_option pp.all true in
#check @fee_slot_has_only_fixed_spends_outputs
#print axioms fee_slot_has_only_fixed_spends_outputs
set_option pp.all true in
#check @retained_action_success_consequence
#print axioms retained_action_success_consequence
set_option pp.all true in
#check @admitted_retained_slot_success
#print axioms admitted_retained_slot_success

end ShielddSecurity.TransferProjection
