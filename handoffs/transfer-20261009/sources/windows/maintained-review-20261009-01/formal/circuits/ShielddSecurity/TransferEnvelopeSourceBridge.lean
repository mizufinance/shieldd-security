import ShielddSecurity.TransferProofAdmissionModel

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferEnvelopeSourceBridge

open TransferAcceptance TransferProofAdmissionModel

/-!
The decoded claim view is obtained from the exact retained Item.envelope by an
independent decoder function. Successful framing derives this association and
original item order. There is no association or native Transfer validity premise.
The native Envelope parser/serializer correspondence, bounded canonical scalar
and group decoding, registry/setup, transcripts and cryptographic verification
contracts remain separate. The native API retains decoded Envelope values; its
serializer/decoder view must instantiate this function consistently.
-/

def decodeEntries (decode : List Nat → Option ClaimContext) :
    List Item → Option (List Entry)
  | [] => some []
  | item :: rest =>
      match decode item.envelope with
      | none => none
      | some claim =>
          match decodeEntries decode rest with
          | none => none
          | some entries => some (⟨item, claim⟩ :: entries)

def verifyEncodedIndividual (decode : List Nat → Option ClaimContext)
    (registry : Registry) (item : Item) (individualVerified : Bool) : Option Capability :=
  match decode item.envelope with
  | none => none
  | some claim => verifyIndividual registry ⟨item, claim⟩ individualVerified

def verifyEncodedBatch (decode : List Nat → Option ClaimContext)
    (registry : Registry) (items : List Item) (batchVerified : Bool) : Option (List Capability) :=
  match decodeEntries decode items with
  | none => none
  | some entries => verifyBatch registry entries batchVerified

theorem decoded_entries_same_source (decode : List Nat → Option ClaimContext)
    (items : List Item) (entries : List Entry)
    (success : decodeEntries decode items = some entries) :
    entries.map Entry.item = items ∧
      ∀ entry ∈ entries, decode entry.item.envelope = some entry.claim := by
  induction items generalizing entries with
  | nil =>
      have same : [] = entries := Option.some.inj success
      subst entries
      exact ⟨rfl, by simp⟩
  | cons item rest ih =>
      cases decoded : decode item.envelope with
      | none =>
          simp only [decodeEntries, decoded] at success
          cases success
      | some claim =>
          cases tail : decodeEntries decode rest with
          | none =>
              simp only [decodeEntries, decoded, tail] at success
              cases success
          | some remaining =>
              have same : (⟨item, claim⟩ : Entry) :: remaining = entries := Option.some.inj
                (by simpa only [decodeEntries, decoded, tail] using success)
              subst entries
              have complete := ih remaining tail
              constructor
              · simpa only [List.map_cons] using congrArg (List.cons item) complete.1
              · intro entry inside
                rcases List.mem_cons.mp inside with same | present
                · subst entry
                  exact decoded
                · exact complete.2 entry present

theorem invalid_envelope_unavailable (decode : List Nat → Option ClaimContext)
    (registry : Registry) (item : Item) (individualVerified : Bool)
    (invalid : decode item.envelope = none) :
    verifyEncodedIndividual decode registry item individualVerified = none := by
  simp only [verifyEncodedIndividual, invalid]

theorem individual_envelope_join (decode : List Nat → Option ClaimContext)
    (registry : Registry) (item : Item) (individualVerified : Bool) (capability : Capability)
    (success : verifyEncodedIndividual decode registry item individualVerified = some capability) :
    ∃ claim relation, decode item.envelope = some claim ∧
      registry.relation item.family = some relation ∧
      ClaimBound item.family relation item.statement claim ∧ individualVerified = true ∧
      capability.registry = registry.identity ∧ capability.item = item := by
  cases decoded : decode item.envelope with
  | none =>
      simp only [verifyEncodedIndividual, decoded] at success
      cases success
  | some claim =>
      have checked : verifyIndividual registry ⟨item, claim⟩ individualVerified = some capability :=
        by simpa only [verifyEncodedIndividual, decoded] using success
      obtain ⟨relation, lookup, bound, verified, _⟩ :=
        individual_success registry ⟨item, claim⟩ individualVerified capability checked
      have exactItem := individual_exact_capability registry ⟨item, claim⟩
        individualVerified capability checked
      exact ⟨claim, relation, rfl, lookup, bound, verified, exactItem⟩

theorem batch_envelope_join (decode : List Nat → Option ClaimContext)
    (registry : Registry) (items : List Item) (batchVerified : Bool)
    (capabilities : List Capability)
    (success : verifyEncodedBatch decode registry items batchVerified = some capabilities) :
    ∃ first rest relation,
      decodeEntries decode items = some (first :: rest) ∧
      (first :: rest).map Entry.item = items ∧
      (∀ entry ∈ first :: rest, decode entry.item.envelope = some entry.claim) ∧
      registry.relation first.item.family = some relation ∧
      (∀ entry ∈ first :: rest, ContextBound first.item.family relation entry) ∧
      batchVerified = true ∧ capabilities.map Capability.item = items ∧
      (∀ capability ∈ capabilities, capability.registry = registry.identity) := by
  cases decoded : decodeEntries decode items with
  | none =>
      simp only [verifyEncodedBatch, decoded] at success
      cases success
  | some entries =>
      have checked : verifyBatch registry entries batchVerified = some capabilities :=
        by simpa only [verifyEncodedBatch, decoded] using success
      cases entries with
      | nil =>
          simp only [verifyBatch] at checked
          cases checked
      | cons first rest =>
          have source := decoded_entries_same_source decode items (first :: rest) decoded
          obtain ⟨relation, lookup, contexts, verified, _⟩ :=
            batch_success registry first rest batchVerified capabilities checked
          have order := (batch_exact_order registry first rest batchVerified capabilities checked).1
          have registered := batch_exact_registry registry first rest batchVerified capabilities checked
          exact ⟨first, rest, relation, rfl, source.1, source.2, lookup, contexts,
            verified, order.trans source.1, registered⟩

set_option pp.all true in
#check @decoded_entries_same_source
#print axioms decoded_entries_same_source
set_option pp.all true in
#check @invalid_envelope_unavailable
#print axioms invalid_envelope_unavailable
set_option pp.all true in
#check @individual_envelope_join
#print axioms individual_envelope_join
set_option pp.all true in
#check @batch_envelope_join
#print axioms batch_envelope_join

end ShielddSecurity.TransferEnvelopeSourceBridge
