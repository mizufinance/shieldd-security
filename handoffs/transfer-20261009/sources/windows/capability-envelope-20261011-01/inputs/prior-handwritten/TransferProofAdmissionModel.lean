import ShielddSecurity.TransferAcceptance

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferProofAdmissionModel

open TransferAcceptance

/-!
Independent executable model of the owned Registry and Envelope admission
framing. The relation is selected by the local registry from the item family.
The claim is the decoded view of the same envelope retained by that item;
establishing that byte/claim correspondence remains a native codec obligation.

The verifier-result input represents either an individual Pari verification or
the separate fresh-randomized batch verification. These are separate global
cryptographic contracts. A true result does not establish Transfer semantics
here. No per-entry cryptographic consequence is inferred from batch success.
-/

structure Registry where
  identity : Nat
  relation : Nat → Option Nat

structure Entry where
  item : Item
  claim : ClaimContext

def mint (registry : Registry) (entry : Entry) : Capability :=
  ⟨registry.identity, entry.item⟩

def ContextBound (family relation : Nat) (entry : Entry) : Prop :=
  entry.item.family = family ∧
    ClaimBound family relation entry.item.statement entry.claim

instance (family relation : Nat) (entry : Entry) :
    Decidable (ContextBound family relation entry) := by
  unfold ContextBound ClaimBound
  infer_instance

instance (family relation statement : Nat) (claim : ClaimContext) :
    Decidable (ClaimBound family relation statement claim) := by
  unfold ClaimBound
  infer_instance

def checkContexts (family relation : Nat) : List Entry → Option Unit
  | [] => some ()
  | entry :: rest =>
      if ContextBound family relation entry then checkContexts family relation rest else none

def verifyIndividual (registry : Registry) (entry : Entry)
    (individualVerified : Bool) : Option Capability :=
  match registry.relation entry.item.family with
  | none => none
  | some relation =>
      if ClaimBound entry.item.family relation entry.item.statement entry.claim then
        if individualVerified then some (mint registry entry) else none
      else none

def verifyBatch (registry : Registry) (entries : List Entry)
    (batchVerified : Bool) : Option (List Capability) :=
  match entries with
  | [] => none
  | first :: rest =>
      match registry.relation first.item.family with
      | none => none
      | some relation =>
          match checkContexts first.item.family relation (first :: rest) with
          | none => none
          | some _ =>
              if batchVerified then some ((first :: rest).map (mint registry)) else none

theorem check_contexts_success (family relation : Nat) (entries : List Entry)
    (success : checkContexts family relation entries = some ()) :
    ∀ entry ∈ entries, ContextBound family relation entry := by
  induction entries with
  | nil => simp
  | cons first rest ih =>
      by_cases bound : ContextBound family relation first
      · have tail : checkContexts family relation rest = some () := by
          simpa only [checkContexts, if_pos bound] using success
        intro entry inside
        rcases List.mem_cons.mp inside with same | present
        · subst entry
          exact bound
        · exact ih tail entry present
      · simp only [checkContexts, if_neg bound] at success
        cases success

theorem missing_individual_key_unavailable (registry : Registry) (entry : Entry)
    (individualVerified : Bool) (missing : registry.relation entry.item.family = none) :
    verifyIndividual registry entry individualVerified = none := by
  simp only [verifyIndividual, missing]

theorem individual_success (registry : Registry) (entry : Entry)
    (individualVerified : Bool) (capability : Capability)
    (success : verifyIndividual registry entry individualVerified = some capability) :
    ∃ relation, registry.relation entry.item.family = some relation ∧
      ClaimBound entry.item.family relation entry.item.statement entry.claim ∧
      individualVerified = true ∧ capability = mint registry entry := by
  cases lookup : registry.relation entry.item.family with
  | none =>
      simp only [verifyIndividual, lookup] at success
      cases success
  | some relation =>
      by_cases bound : ClaimBound entry.item.family relation entry.item.statement entry.claim
      · cases individualVerified with
        | false =>
            simp [verifyIndividual, lookup, bound] at success
        | true =>
            have same : mint registry entry = capability := Option.some.inj
              (by simpa [verifyIndividual, lookup, bound] using success)
            exact ⟨relation, rfl, bound, rfl, same.symm⟩
      · simp only [verifyIndividual, lookup, if_neg bound] at success
        cases success

theorem individual_exact_capability (registry : Registry) (entry : Entry)
    (individualVerified : Bool) (capability : Capability)
    (success : verifyIndividual registry entry individualVerified = some capability) :
    capability.registry = registry.identity ∧ capability.item = entry.item := by
  obtain ⟨_, _, _, _, exactItem⟩ :=
    individual_success registry entry individualVerified capability success
  rw [exactItem]
  exact ⟨rfl, rfl⟩

theorem empty_batch_unavailable (registry : Registry) (batchVerified : Bool) :
    verifyBatch registry [] batchVerified = none := rfl

theorem missing_batch_key_unavailable (registry : Registry) (first : Entry)
    (rest : List Entry) (batchVerified : Bool)
    (missing : registry.relation first.item.family = none) :
    verifyBatch registry (first :: rest) batchVerified = none := by
  simp only [verifyBatch, missing]

theorem batch_success (registry : Registry) (first : Entry) (rest : List Entry)
    (batchVerified : Bool) (capabilities : List Capability)
    (success : verifyBatch registry (first :: rest) batchVerified = some capabilities) :
    ∃ relation, registry.relation first.item.family = some relation ∧
      (∀ entry ∈ first :: rest, ContextBound first.item.family relation entry) ∧
      batchVerified = true ∧ capabilities = (first :: rest).map (mint registry) := by
  cases lookup : registry.relation first.item.family with
  | none =>
      simp only [verifyBatch, lookup] at success
      cases success
  | some relation =>
      cases checked : checkContexts first.item.family relation (first :: rest) with
      | none =>
          simp only [verifyBatch, lookup, checked] at success
          cases success
      | some unit =>
          cases unit
          cases batchVerified with
          | false =>
              simp [verifyBatch, lookup, checked] at success
          | true =>
              have same : (first :: rest).map (mint registry) = capabilities := Option.some.inj
                (by simpa [verifyBatch, lookup, checked] using success)
              exact ⟨relation, rfl,
                check_contexts_success first.item.family relation (first :: rest) checked,
                rfl, same.symm⟩

theorem batch_exact_order (registry : Registry) (first : Entry) (rest : List Entry)
    (batchVerified : Bool) (capabilities : List Capability)
    (success : verifyBatch registry (first :: rest) batchVerified = some capabilities) :
    capabilities.map Capability.item = (first :: rest).map Entry.item ∧
      capabilities.length = (first :: rest).length := by
  obtain ⟨_, _, _, _, exactItems⟩ :=
    batch_success registry first rest batchVerified capabilities success
  rw [exactItems]
  constructor
  · simp only [List.map_map, Function.comp_def, mint]
  · simp only [List.length_map]

theorem batch_exact_registry (registry : Registry) (first : Entry) (rest : List Entry)
    (batchVerified : Bool) (capabilities : List Capability)
    (success : verifyBatch registry (first :: rest) batchVerified = some capabilities) :
    ∀ capability ∈ capabilities, capability.registry = registry.identity := by
  obtain ⟨_, _, _, _, exactItems⟩ :=
    batch_success registry first rest batchVerified capabilities success
  rw [exactItems]
  intro capability inside
  obtain ⟨entry, _, same⟩ := List.mem_map.mp inside
  rw [← same]
  rfl

theorem batch_family_gate (registry : Registry) (first : Entry) (rest : List Entry)
    (batchVerified : Bool) (capabilities : List Capability)
    (success : verifyBatch registry (first :: rest) batchVerified = some capabilities) :
    FamilyBatch first.item.family ((first :: rest).map Entry.item) := by
  obtain ⟨_, _, contexts, _, _⟩ :=
    batch_success registry first rest batchVerified capabilities success
  constructor
  · simp
  · intro item inside
    obtain ⟨entry, present, same⟩ := List.mem_map.mp inside
    rw [← same]
    exact (contexts entry present).1

theorem individual_wrong_relation_refused (registry : Registry) (entry : Entry)
    (individualVerified : Bool) (relation : Nat)
    (lookup : registry.relation entry.item.family = some relation)
    (wrong : entry.claim.relation ≠ relation) :
    ¬ ∃ capability, verifyIndividual registry entry individualVerified = some capability := by
  rintro ⟨capability, success⟩
  obtain ⟨selected, selectedKey, bound, _, _⟩ :=
    individual_success registry entry individualVerified capability success
  have same : selected = relation := Option.some.inj (selectedKey.symm.trans lookup)
  exact wrong (bound.2.1.trans same)

theorem individual_wrong_public_refused (registry : Registry) (entry : Entry)
    (individualVerified : Bool) (wrong : entry.claim.publicInputs ≠ [entry.item.statement]) :
    ¬ ∃ capability, verifyIndividual registry entry individualVerified = some capability := by
  rintro ⟨capability, success⟩
  obtain ⟨_, _, bound, _, _⟩ :=
    individual_success registry entry individualVerified capability success
  exact wrong bound.2.2.1

theorem individual_wrong_commitment_shape_refused (registry : Registry) (entry : Entry)
    (individualVerified : Bool) (wrong : entry.claim.commitments.length ≠ 1) :
    ¬ ∃ capability, verifyIndividual registry entry individualVerified = some capability := by
  rintro ⟨capability, success⟩
  obtain ⟨_, _, bound, _, _⟩ :=
    individual_success registry entry individualVerified capability success
  exact wrong bound.2.2.2

theorem batch_wrong_family_refused (registry : Registry) (first entry : Entry)
    (rest : List Entry) (batchVerified : Bool) (inside : entry ∈ first :: rest)
    (wrong : entry.item.family ≠ first.item.family) :
    ¬ ∃ capabilities, verifyBatch registry (first :: rest) batchVerified = some capabilities := by
  rintro ⟨capabilities, success⟩
  obtain ⟨_, _, contexts, _, _⟩ :=
    batch_success registry first rest batchVerified capabilities success
  exact wrong (contexts entry inside).1

set_option pp.all true in
#check @check_contexts_success
#print axioms check_contexts_success
set_option pp.all true in
#check @missing_individual_key_unavailable
#print axioms missing_individual_key_unavailable
set_option pp.all true in
#check @individual_success
#print axioms individual_success
set_option pp.all true in
#check @individual_exact_capability
#print axioms individual_exact_capability
set_option pp.all true in
#check @empty_batch_unavailable
#print axioms empty_batch_unavailable
set_option pp.all true in
#check @missing_batch_key_unavailable
#print axioms missing_batch_key_unavailable
set_option pp.all true in
#check @batch_success
#print axioms batch_success
set_option pp.all true in
#check @batch_exact_order
#print axioms batch_exact_order
set_option pp.all true in
#check @batch_exact_registry
#print axioms batch_exact_registry
set_option pp.all true in
#check @batch_family_gate
#print axioms batch_family_gate
set_option pp.all true in
#check @individual_wrong_relation_refused
#print axioms individual_wrong_relation_refused
set_option pp.all true in
#check @individual_wrong_public_refused
#print axioms individual_wrong_public_refused
set_option pp.all true in
#check @individual_wrong_commitment_shape_refused
#print axioms individual_wrong_commitment_shape_refused
set_option pp.all true in
#check @batch_wrong_family_refused
#print axioms batch_wrong_family_refused

end ShielddSecurity.TransferProofAdmissionModel
