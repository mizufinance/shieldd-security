import ShielddSecurity.TransferProjection

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferTransaction

open TransferAcceptance TransferAdmission TransferExecution TransferProjection

/-!
Scoped application composition for an unbounded ordered list of retained
Transfer occurrences. The native caller supplies exact locations, decoded body
and complete routing entry identity. The same indexed body supplies its Item and
its executable effects. Ordinary daily replay is checked before fixed spends;
routing follows each slot and the transaction index follows the whole list.
The initial state is the entry to this modeled Transfer effect portion. Native
pay_fee/audit/source writes and mixed-family actions are outside this portion;
the savepoint theorem restores this model's entry snapshot, not an asserted
native accounting or durable-store snapshot.

This is an independent executable model, not a Rust refinement. The actual
mixed-family slot extraction, canonical codecs, full64-field/hash/public/committed
joins, routing position construction, source/time/compliance admission, store
errors and participating-store durability remain explicit external boundaries.
A semantic verifiedContract still requires matching valid keys, upstream proof
knowledge and the full Transfer row-to-semantic interpretation. No hash inversion,
opaque conservation or supplied desired poststate appears in these proofs.
-/

structure RoutedSlot where
  location : Slot
  body : NativeBody
  route : Nat

/-- Reuses current ordinary-volume admission before any fixed-slot mutation. -/
def runRoutedSlot (state : EffectState) (entry : RoutedSlot) : Option EffectState :=
  if entry.body.ordinaryContext = slotContext entry.location then
    (runVolumeCheckedTransfer state (slotContext entry.location) (projectEffects entry.body)).bind
      (fun middle => effectStep middle (.route entry.route))
  else none

def applyRoutedSlot (state : EffectState) (entry : RoutedSlot) : EffectState :=
  { appliedTransfer state (slotContext entry.location) (projectEffects entry.body) with
    routing := state.routing ++ [entry.route] }

def runRoutedSlots (state : EffectState) : List RoutedSlot → Option EffectState
  | [] => some state
  | entry :: rest => (runRoutedSlot state entry).bind (fun middle => runRoutedSlots middle rest)

def applyRoutedSlots (state : EffectState) : List RoutedSlot → EffectState
  | [] => state
  | entry :: rest => applyRoutedSlots (applyRoutedSlot state entry) rest

def runRoutedTransaction (state : EffectState) (entries : List RoutedSlot)
    (transaction : Nat) : Option EffectState :=
  (runRoutedSlots state entries).bind (fun middle => effectStep middle (.index transaction))

def applyRoutedTransaction (state : EffectState) (entries : List RoutedSlot)
    (transaction : Nat) : EffectState :=
  let working := applyRoutedSlots state entries
  { working with transactionIndex := working.transactionIndex ++ [transaction] }

def spendEntries (entry : RoutedSlot) : List Nat := [entry.body.spend0, entry.body.spend1]
def outputEntries (entry : RoutedSlot) : List Nat := [entry.body.output0.payload, entry.body.output1.payload]
def volumeEntries (entry : RoutedSlot) : List (Nat × Nat) :=
  if slotContext entry.location then [(entry.body.volume.day, entry.body.volume.nullifier)] else []
def volumePayloadEntries (entry : RoutedSlot) : List Nat :=
  if slotContext entry.location then [entry.body.volume.payload] else []

theorem volume_checked_success_refines (state after : EffectState)
    (ordinary : Bool) (effects : TransferEffects)
    (success : runVolumeCheckedTransfer state ordinary effects = some after) :
    runEffects state (transferEffects ordinary effects) = some after := by
  by_cases conflict : ordinary = true ∧ (effects.day, effects.volumeNullifier) ∈ state.volumeNullifiers
  · simp [runVolumeCheckedTransfer, conflict] at success
  · simpa [runVolumeCheckedTransfer, conflict] using success

/-- Readiness, context and exact intermediate state follow from model success. -/
theorem routed_slot_success (state after : EffectState) (entry : RoutedSlot)
    (success : runRoutedSlot state entry = some after) :
    entry.body.ordinaryContext = slotContext entry.location ∧
    SpendReady state entry.body.spend0 entry.body.spend1 ∧
    (slotContext entry.location = true →
      (entry.body.volume.day, entry.body.volume.nullifier) ∉ state.volumeNullifiers) ∧
    after = applyRoutedSlot state entry := by
  by_cases context : entry.body.ordinaryContext = slotContext entry.location
  · cases result : runVolumeCheckedTransfer state (slotContext entry.location) (projectEffects entry.body) with
    | none => simp [runRoutedSlot, context, result] at success
    | some middle =>
        have transferSuccess := volume_checked_success_refines state middle _ _ result
        obtain ⟨ready, fresh, exactMiddle⟩ := successful_transfer_exact state middle _ _ transferSuccess
        have routed : { middle with routing := middle.routing ++ [entry.route] } = after := by
          exact Option.some.inj (by simpa [runRoutedSlot, context, result, effectStep] using success)
        rw [exactMiddle] at routed
        exact ⟨context, ready, fresh, by simpa [applyRoutedSlot, appliedTransfer] using routed.symm⟩
  · simp [runRoutedSlot, context] at success

theorem routed_slots_success_exact (state after : EffectState) (entries : List RoutedSlot)
    (success : runRoutedSlots state entries = some after) :
    after = applyRoutedSlots state entries := by
  induction entries generalizing state with
  | nil => exact (Option.some.inj success).symm
  | cons entry rest ih =>
      cases result : runRoutedSlot state entry with
      | none => simp [runRoutedSlots, result] at success
      | some middle =>
          have tailSuccess : runRoutedSlots middle rest = some after := by
            simpa [runRoutedSlots, result] using success
          have exactHead := (routed_slot_success state middle entry result).2.2.2
          simpa [applyRoutedSlots, exactHead] using ih middle tailSuccess

theorem routed_slots_success_contexts (state after : EffectState) (entries : List RoutedSlot)
    (success : runRoutedSlots state entries = some after) :
    ∀ entry ∈ entries, entry.body.ordinaryContext = slotContext entry.location := by
  induction entries generalizing state with
  | nil => simp
  | cons head rest ih =>
      cases result : runRoutedSlot state head with
      | none => simp [runRoutedSlots, result] at success
      | some middle =>
          have tailSuccess : runRoutedSlots middle rest = some after := by
            simpa [runRoutedSlots, result] using success
          intro entry inside
          rcases List.mem_cons.mp inside with same | tail
          · subst entry
            exact (routed_slot_success state middle head result).1
          · exact ih middle tailSuccess entry tail

/-- Ordered occurrence lists preserve both slots, equal output payloads and all
ordinary volume entries; fee slots contribute empty volume lists. -/
theorem applied_slots_fields (state : EffectState) (entries : List RoutedSlot) :
    (applyRoutedSlots state entries).pendingNullifiers = state.pendingNullifiers ++ entries.flatMap spendEntries ∧
    (applyRoutedSlots state entries).notes = state.notes ++ entries.flatMap outputEntries ∧
    (applyRoutedSlots state entries).volumeNullifiers = state.volumeNullifiers ++ entries.flatMap volumeEntries ∧
    (applyRoutedSlots state entries).volumePayloads = state.volumePayloads ++ entries.flatMap volumePayloadEntries ∧
    (applyRoutedSlots state entries).routing = state.routing ++ entries.map RoutedSlot.route ∧
    (applyRoutedSlots state entries).transactionIndex = state.transactionIndex ∧
    (applyRoutedSlots state entries).durableNullifiers = state.durableNullifiers := by
  induction entries generalizing state with
  | nil => simp [applyRoutedSlots]
  | cons entry rest ih =>
      simpa [applyRoutedSlots, applyRoutedSlot, appliedTransfer, projectEffects,
        spendEntries, outputEntries, volumeEntries, volumePayloadEntries, List.append_assoc]
        using ih (applyRoutedSlot state entry)

theorem routed_transaction_success_exact (state after : EffectState)
    (entries : List RoutedSlot) (transaction : Nat)
    (success : runRoutedTransaction state entries transaction = some after) :
    after = applyRoutedTransaction state entries transaction := by
  cases result : runRoutedSlots state entries with
  | none => simp [runRoutedTransaction, result] at success
  | some middle =>
      have exactSlots := routed_slots_success_exact state middle entries result
      have indexed : { middle with transactionIndex := middle.transactionIndex ++ [transaction] } = after := by
        exact Option.some.inj (by simpa [runRoutedTransaction, result, effectStep] using success)
      rw [exactSlots] at indexed
      simpa [applyRoutedTransaction] using indexed.symm

theorem routed_transaction_success_fields (state after : EffectState)
    (entries : List RoutedSlot) (transaction : Nat)
    (success : runRoutedTransaction state entries transaction = some after) :
    after.pendingNullifiers = state.pendingNullifiers ++ entries.flatMap spendEntries ∧
    after.notes = state.notes ++ entries.flatMap outputEntries ∧
    after.volumeNullifiers = state.volumeNullifiers ++ entries.flatMap volumeEntries ∧
    after.volumePayloads = state.volumePayloads ++ entries.flatMap volumePayloadEntries ∧
    after.routing = state.routing ++ entries.map RoutedSlot.route ∧
    after.transactionIndex = state.transactionIndex ++ [transaction] ∧
    after.durableNullifiers = state.durableNullifiers := by
  rw [routed_transaction_success_exact state after entries transaction success]
  obtain ⟨spends, outputs, volumes, volumePayloads, routes, index, durable⟩ := applied_slots_fields state entries
  exact ⟨spends, outputs, volumes, volumePayloads, routes,
    by simpa [applyRoutedTransaction, index], durable⟩

theorem failed_routed_transaction_restores_snapshot (state : EffectState)
    (entries : List RoutedSlot) (transaction : Nat)
    (failure : runRoutedTransaction state entries transaction = none) :
    applySavepoint state (runRoutedTransaction state entries transaction) = state := by
  simp [failure, applySavepoint]

/-- Exact rows bind every indexed retained Item. The full semantic verified
contract remains conditional; poststate and all contexts are derived from this
same indexed body's successful ordered program, never supplied as conclusions. -/
theorem admitted_routed_transaction_consequence
    (family : Nat) (fields : NativeBody → List Nat) (hash : List Nat → Nat)
    (envelopes : Nat → List Nat) (entries : Nat → RoutedSlot)
    (slots : List Nat) (rows : List (Nat × Capability)) (registry : Nat)
    (contract : Item → Prop)
    (bound : BoundRows slots
      (fun index => (retainAction family fields hash (envelopes index) (entries index).body).item)
      rows registry)
    (verifiedContract : ∀ row ∈ rows, row.2.registry = registry → contract row.2.item)
    (state after : EffectState) (transaction : Nat)
    (success : runRoutedTransaction state (slots.map entries) transaction = some after) :
    (∀ index ∈ slots, contract (retainAction family fields hash (envelopes index) (entries index).body).item) ∧
    (∀ entry ∈ slots.map entries, entry.body.ordinaryContext = slotContext entry.location) ∧
    after = applyRoutedTransaction state (slots.map entries) transaction := by
  refine ⟨?_, ?_, routed_transaction_success_exact state after _ transaction success⟩
  · intro index inside
    exact expected_slots_satisfy_contract slots
      (fun i => (retainAction family fields hash (envelopes i) (entries i).body).item)
      rows registry contract bound verifiedContract index inside
  · cases result : runRoutedSlots state (slots.map entries) with
    | none => simp [runRoutedTransaction, result] at success
    | some middle => exact routed_slots_success_contexts state middle _ result

set_option pp.all true in
#check @volume_checked_success_refines
#print axioms volume_checked_success_refines
set_option pp.all true in
#check @routed_slot_success
#print axioms routed_slot_success
set_option pp.all true in
#check @routed_slots_success_exact
#print axioms routed_slots_success_exact
set_option pp.all true in
#check @routed_slots_success_contexts
#print axioms routed_slots_success_contexts
set_option pp.all true in
#check @applied_slots_fields
#print axioms applied_slots_fields
set_option pp.all true in
#check @routed_transaction_success_exact
#print axioms routed_transaction_success_exact
set_option pp.all true in
#check @routed_transaction_success_fields
#print axioms routed_transaction_success_fields
set_option pp.all true in
#check @failed_routed_transaction_restores_snapshot
#print axioms failed_routed_transaction_restores_snapshot
set_option pp.all true in
#check @admitted_routed_transaction_consequence
#print axioms admitted_routed_transaction_consequence

end ShielddSecurity.TransferTransaction
