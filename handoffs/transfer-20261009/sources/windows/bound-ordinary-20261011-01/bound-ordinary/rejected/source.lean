import ShielddSecurity.TransferOrdinaryStorageSource01
import ShielddSecurity.TransferVerificationEqualitySource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBoundOrdinarySource01

open TransferStateDelta TransferRawStateProgram01
open TransferVerificationEqualitySource01 (Item)

/-! Execute the actual modeled stateless re-extraction and whole Verification
comparison before the installed Ordinary note/volume SCT program. The token
is explicitly Ordinary. Extractor semantics, validated-token provenance,
cryptographic truth, Rust ownership/tree/store/codecs and durability remain
interfaces. Equality of the compared scalar is not equality of its preimages.
Returned raw errors may retain earlier object/event effects until delivery
discards the child. No native control or full certification follows. -/

def executeBound {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E) :
    Outcome O E (TransferCapabilitySource01.Error K (TransferSctInsertionSource01.Error X)) :=
  TransferCapabilitySource01.execute
    (TransferOrdinaryStorageSource01.installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
    extract inputs outputs wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child

theorem liftRaw_preserves_cache_selection {O E K X : Type}
    (returned : Outcome O E (TransferRawEffectsSource01.EffectError X)) :
    asCache (TransferCapabilitySource01.liftRaw (K := K) returned) = asCache returned := by
  cases observed : returned.result with
  | error error => simp only [TransferCapabilitySource01.liftRaw, observed, asCache]
  | ok returnedUnit => cases returnedUnit; simp only [TransferCapabilitySource01.liftRaw, observed, asCache]

theorem any_return_preserves_input_nonverifiable_writes {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E) :
    (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child).cache.nonverifiable = child.cache.nonverifiable := by
  cases observed : extract action .ordinary with
  | error error => simp only [executeBound, TransferCapabilitySource01.execute, observed]
  | ok current =>
    by_cases matched : current = item
    · simp only [executeBound, TransferCapabilitySource01.execute, observed, if_pos matched,
        TransferCapabilitySource01.liftRaw, TransferCapabilitySource01.isOrdinary]
      exact (TransferOrdinaryStorageSource01.execution_preserves_nv_and_only_adds_volume_markers raw notes volume sct available
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)).1
    · simp only [executeBound, TransferCapabilitySource01.execute, observed, if_neg matched]

theorem family_mismatch_precedes_every_effect {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item current : Item) (child : Delta O E)
    (observed : extract action .ordinary = .ok current) (different : current.family ≠ item.family) :
    executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child = ⟨child.cache, .error .mismatch⟩ := by
  have mismatch : current ≠ item := by
    intro equal
    exact different (congrArg Item.family equal)
  exact TransferCapabilitySource01.different_item_precedes_effects _ extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child current observed mismatch

theorem statement_scalar_mismatch_precedes_every_effect {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item current : Item) (child : Delta O E)
    (observed : extract action .ordinary = .ok current) (different : current.statement ≠ item.statement) :
    executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child = ⟨child.cache, .error .mismatch⟩ := by
  have mismatch : current ≠ item := by
    intro equal
    exact different (congrArg Item.statement equal)
  exact TransferCapabilitySource01.different_item_precedes_effects _ extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child current observed mismatch

theorem envelope_mismatch_precedes_every_effect {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item current : Item) (child : Delta O E)
    (observed : extract action .ordinary = .ok current) (different : current.envelope ≠ item.envelope) :
    executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child = ⟨child.cache, .error .mismatch⟩ := by
  have mismatch : current ≠ item := by
    intro equal
    exact different (congrArg Item.envelope equal)
  exact TransferCapabilitySource01.different_item_precedes_effects _ extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child current observed mismatch

theorem successful_body_derives_reextraction_freshness_and_markers {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E)
    (success : (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child).result = .ok ()) :
    extract action .ordinary = .ok item ∧ (applyCache child.parent child.cache).verifiable entryKey = none ∧
      (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
        payload nullifierKey entryKey dayKey action item child).cache.verifiable =
          (TransferRawEffectsSource01.putV (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]).verifiable ∧
      (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
        payload nullifierKey entryKey dayKey action item child).cache.nonverifiable = child.cache.nonverifiable := by
  have observed := TransferCapabilitySource01.successful_execution_derives_exact_reextraction _ extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child success
  have dispatch : executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child =
      TransferCapabilitySource01.liftRaw (K := K) (TransferOrdinaryStorageSource01.execute raw notes volume sct available
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)) :=
    TransferCapabilitySource01.exact_rebinding_dispatches_projected_action _ extract inputs outputs
      wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child observed
  have rawSuccess : (TransferOrdinaryStorageSource01.execute raw notes volume sct available
      wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)).result = .ok () := by
    cases result : (TransferOrdinaryStorageSource01.execute raw notes volume sct available
      wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)).result with
    | error error => simp only [dispatch, TransferCapabilitySource01.liftRaw, result] at success; contradiction
    | ok returnedUnit => cases returnedUnit; rfl
  have derived := TransferOrdinaryStorageSource01.execution_success_derives_fresh_input_and_two_writes raw notes volume sct available
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action) rawSuccess
  rw [dispatch]
  exact ⟨observed, derived.2⟩

theorem successful_body_derives_visible_marker_values {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E) (different : entryKey ≠ dayKey)
    (success : (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child).result = .ok ()) :
    (applyCache child.parent (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child).cache).verifiable entryKey = some [1] ∧
      (applyCache child.parent (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
        payload nullifierKey entryKey dayKey action item child).cache).verifiable dayKey = some [1] := by
  have derived := successful_body_derives_reextraction_freshness_and_markers raw notes volume sct available extract inputs outputs
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item child success
  simp [applyCache, derived.2.2.1, TransferRawEffectsSource01.putV, overlay, different]

theorem existing_current_entry_rejects_bound_body {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E) (bytes : Bytes)
    (present : (applyCache child.parent child.cache).verifiable entryKey = some bytes) :
    asCache (executeBound raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item child) = none := by
  have rejected : asCache (TransferOrdinaryStorageSource01.execute raw notes volume sct available
      wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)) = none :=
    TransferCurrentVolumeSource01.existing_current_volume_excludes_success
      (TransferOrdinaryStorageSource01.installVolume raw volume sct treeKey volumeKey payload) notes sct available
      wordMax capacity treeKey notesKey nullifierKey entryKey dayKey true child (inputs action) (outputs action) bytes present
  cases observed : extract action .ordinary with
  | error error => simp only [executeBound, TransferCapabilitySource01.execute, observed, asCache]
  | ok current =>
    by_cases matched : current = item
    · rw [matched] at observed
      rw [TransferCapabilitySource01.exact_rebinding_dispatches_projected_action _ extract inputs outputs
        wordMax capacity nullifierKey entryKey dayKey action ⟨item, .ordinary⟩ child observed]
      rw [liftRaw_preserves_cache_selection]
      exact rejected
    · simp only [executeBound, TransferCapabilitySource01.execute, observed, if_neg matched, asCache]

def deliveryApi {O E K X Tree A T : Type} (api : Api O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) : Api O E T :=
  {api with execute := (fun child => asCache (executeBound raw notes volume sct available extract inputs outputs
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item child))}

theorem existing_parent_entry_rejects_bound_delivery {O E K X Tree A T : Type} (api : Api O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (bytes : Bytes) (present : parent.verifiable entryKey = some bytes) :
    run (deliveryApi api raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item) registryMatches exclusive mode transaction parent queued = none := by
  have currentPresent : (applyCache parent (empty (O := O) (E := E))).verifiable entryKey = some bytes := by
    rw [apply_empty]
    exact present
  have rejected := existing_current_entry_rejects_bound_body raw notes volume sct available extract inputs outputs
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item ⟨parent, empty⟩ bytes currentPresent
  cases registryMatches with
  | false => rfl
  | true =>
    cases exclusive with
    | false => rfl
    | true => simp only [run, begin, deliveryApi, ↓reduceIte, Option.bind_some, rejected, Option.bind_none]

theorem existing_parent_entry_preserves_parent_and_queue {O E K X Tree A T : Type} (api : Api O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (bytes : Bytes) (present : parent.verifiable entryKey = some bytes) :
    finish parent queued (run (deliveryApi api raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey action item) registryMatches exclusive mode transaction parent queued) = (parent, queued) := by
  exact delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _
    (existing_parent_entry_rejects_bound_delivery api raw notes volume sct available extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item registryMatches exclusive mode transaction parent queued bytes present)

set_option pp.all true in
#check @executeBound
#print axioms executeBound
set_option pp.all true in
#check @liftRaw_preserves_cache_selection
#print axioms liftRaw_preserves_cache_selection
set_option pp.all true in
#check @any_return_preserves_input_nonverifiable_writes
#print axioms any_return_preserves_input_nonverifiable_writes
set_option pp.all true in
#check @family_mismatch_precedes_every_effect
#print axioms family_mismatch_precedes_every_effect
set_option pp.all true in
#check @statement_scalar_mismatch_precedes_every_effect
#print axioms statement_scalar_mismatch_precedes_every_effect
set_option pp.all true in
#check @envelope_mismatch_precedes_every_effect
#print axioms envelope_mismatch_precedes_every_effect
set_option pp.all true in
#check @successful_body_derives_reextraction_freshness_and_markers
#print axioms successful_body_derives_reextraction_freshness_and_markers
set_option pp.all true in
#check @successful_body_derives_visible_marker_values
#print axioms successful_body_derives_visible_marker_values
set_option pp.all true in
#check @existing_current_entry_rejects_bound_body
#print axioms existing_current_entry_rejects_bound_body
set_option pp.all true in
#check @deliveryApi
#print axioms deliveryApi
set_option pp.all true in
#check @existing_parent_entry_rejects_bound_delivery
#print axioms existing_parent_entry_rejects_bound_delivery
set_option pp.all true in
#check @existing_parent_entry_preserves_parent_and_queue
#print axioms existing_parent_entry_preserves_parent_and_queue

end ShielddSecurity.TransferBoundOrdinarySource01
