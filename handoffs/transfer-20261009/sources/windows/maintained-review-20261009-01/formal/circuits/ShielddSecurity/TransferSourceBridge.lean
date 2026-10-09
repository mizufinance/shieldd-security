import ShielddSecurity.TransferTransaction

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferSourceBridge

open TransferAcceptance TransferAdmission TransferProjection TransferTransaction

/-!
Complete-source carrier for the native acceptance/effect join. B represents the
whole decoded source body, not the smaller effect projection NativeBody. The
statement encoder and effect projection are independently defined functions of
the same retained B value; no inverse of an Item hash or injectivity of the
effect projection is assumed. They must still be linked to actual pinned Rust,
codecs, the complete Transfer64 statement and row/native interpretation.

The verifiedContract premise is the explicit upstream/key/relation semantic
contract. The program success premise is an independently executable modeled
admission, not a supplied expected poststate. Native savepoints, mixed families,
deferred indexes, store errors, durable writer and published queries remain
separate bridges. Existing frozen Projection/Transaction proofs are untouched.
-/

structure SourceSlot (B : Type) where
  location : Slot
  body : B
  route : Nat
  envelope : List Nat

def sourceItem {B : Type} (family : Nat) (fields : B → List Nat)
    (hash : List Nat → Nat) (entry : SourceSlot B) : Item :=
  ⟨family, hash (fields entry.body), entry.envelope⟩

def projectSlot {B : Type} (effects : B → NativeBody) (entry : SourceSlot B) : RoutedSlot :=
  ⟨entry.location, effects entry.body, entry.route⟩

theorem full_source_item_derived {B : Type} (family : Nat) (fields : B → List Nat)
    (hash : List Nat → Nat) (entry : SourceSlot B) :
    sourceItem family fields hash entry =
      ⟨family, hash (fields entry.body), entry.envelope⟩ := rfl

theorem full_source_effect_projection {B : Type} (effects : B → NativeBody)
    (entry : SourceSlot B) :
    (projectSlot effects entry).body = effects entry.body ∧
    (projectSlot effects entry).location = entry.location ∧
    (projectSlot effects entry).route = entry.route := ⟨rfl, rfl, rfl⟩

theorem full_source_transaction_consequence {B : Type}
    (family : Nat) (fields : B → List Nat) (hash : List Nat → Nat)
    (effects : B → NativeBody) (entries : Nat → SourceSlot B)
    (slots : List Nat) (rows : List (Nat × Capability)) (registry : Nat)
    (contract : Item → Prop)
    (bound : BoundRows slots (fun i => sourceItem family fields hash (entries i)) rows registry)
    (verifiedContract : ∀ row ∈ rows, row.2.registry = registry → contract row.2.item)
    (state after : EffectState) (transaction : Nat)
    (success : runRoutedTransaction state
      (slots.map fun i => projectSlot effects (entries i)) transaction = some after) :
    (∀ i ∈ slots, contract (sourceItem family fields hash (entries i))) ∧
    (∀ entry ∈ slots.map (fun i => projectSlot effects (entries i)),
      entry.body.ordinaryContext = slotContext entry.location) ∧
    after = applyRoutedTransaction state
      (slots.map fun i => projectSlot effects (entries i)) transaction := by
  refine ⟨?_, ?_, routed_transaction_success_exact state after _ transaction success⟩
  · intro i inside
    exact expected_slots_satisfy_contract slots
      (fun index => sourceItem family fields hash (entries index)) rows registry contract
      bound verifiedContract i inside
  · cases result : runRoutedSlots state
      (slots.map fun i => projectSlot effects (entries i)) with
    | none => simp [runRoutedTransaction, result] at success
    | some middle => exact routed_slots_success_contexts state middle _ result

set_option pp.all true in
#check @full_source_item_derived
#print axioms full_source_item_derived
set_option pp.all true in
#check @full_source_effect_projection
#print axioms full_source_effect_projection
set_option pp.all true in
#check @full_source_transaction_consequence
#print axioms full_source_transaction_consequence

end ShielddSecurity.TransferSourceBridge
