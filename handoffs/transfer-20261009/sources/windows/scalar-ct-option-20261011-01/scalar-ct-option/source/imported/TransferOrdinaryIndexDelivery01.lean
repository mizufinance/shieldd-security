import ShielddSecurity.TransferBoundOrdinarySource01
import ShielddSecurity.TransferIndexInspectionFacts01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOrdinaryIndexDelivery01

open TransferStateDelta TransferRawStateProgram01
open TransferIndexWriterModel01 (Keys Codec Backend Witness)
open TransferVerificationEqualitySource01 (Item)

/-! Successful per-transaction delivery inverts the actual installed body,
height read, index inspection and three NV writes. It preserves body V/object/
event effects. With the qualified bound Ordinary body this derives freshness
and both V markers from the whole enclosing success. It is a child-cache apply
result, not durable block publication. Rust ownership, codecs, key projections,
extractor/proof provenance and authenticated store semantics remain interfaces. -/

def combinedApi {O E T X : Type} (api : Api O E T) (keys : Keys) (codec : Codec)
    (index : Backend O E T) (body : Delta O E → Outcome O E X) : Api O E T :=
  {TransferIndexWriterModel01.indexApi api keys codec index with execute := fun child => asCache (body child)}

theorem selected_cache_derives_success {O E X : Type} (returned : Outcome O E X)
    (selected : Cache O E) (success : asCache returned = some selected) :
    returned.result = .ok () ∧ selected = returned.cache := by
  cases observed : returned.result with
  | error error => simp only [asCache, observed] at success; contradiction
  | ok returnedUnit =>
    cases returnedUnit
    exact ⟨rfl, (Option.some.inj (by simpa only [asCache, observed] using success)).symm⟩

theorem per_transaction_success_recovers_body_height_and_index {O E T X : Type}
    (api : Api O E T) (keys : Keys) (codec : Codec) (index : Backend O E T)
    (body : Delta O E → Outcome O E X) (registryMatches exclusive : Bool)
    (transaction : T) (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (combinedApi api keys codec index body) registryMatches exclusive .perTransaction
      transaction parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧
      ∃ height witness,
        (body ⟨parent, empty⟩).result = .ok () ∧
        api.height ⟨parent, (body ⟨parent, empty⟩).cache⟩ = some height ∧
        TransferIndexWriterModel01.inspect keys codec index height transaction
          ⟨parent, (body ⟨parent, empty⟩).cache⟩ = .ok witness ∧
        committed.parent = applyCache parent
          (TransferIndexWriterModel01.writeIndex keys codec height witness (body ⟨parent, empty⟩).cache) ∧
        committed.events = (body ⟨parent, empty⟩).cache.events ∧ committed.deferred = queued := by
  obtain ⟨registry, unique, executed, prepared, performed, indexed, applied, events, deferred⟩ :=
    successful_delivery_order (combinedApi api keys codec index body) registryMatches exclusive .perTransaction
      transaction parent queued committed success
  change asCache (body ⟨parent, empty⟩) = some executed at performed
  obtain ⟨bodySuccess, selected⟩ := selected_cache_derives_success _ executed performed
  subst executed
  cases heightRead : api.height ⟨parent, (body ⟨parent, empty⟩).cache⟩ with
  | none =>
    simp only [prepareIndex, combinedApi, TransferIndexWriterModel01.indexApi, heightRead, Option.bind_none] at indexed
    contradiction
  | some height =>
    cases indexRead : asCache (TransferIndexWriterModel01.executeIndex keys codec index height transaction
      ⟨parent, (body ⟨parent, empty⟩).cache⟩) with
    | none =>
      simp only [prepareIndex, combinedApi, TransferIndexWriterModel01.indexApi, heightRead,
        Option.bind_some, indexRead, Option.map_none] at indexed
      contradiction
    | some indexedCache =>
      have same : ((⟨parent, indexedCache⟩ : Delta O E), (none : Option T)) = prepared :=
        Option.some.inj (by simpa only [prepareIndex, combinedApi, TransferIndexWriterModel01.indexApi,
          heightRead, Option.bind_some, indexRead, Option.map_some] using indexed)
      subst prepared
      obtain ⟨witness, inspected, written⟩ := TransferIndexWriterModel01.successful_index_writes keys codec index
        height transaction ⟨parent, (body ⟨parent, empty⟩).cache⟩ indexedCache indexRead
      subst indexedCache
      refine ⟨registry, unique, height, witness, bodySuccess, rfl, inspected, applied, ?_, ?_⟩
      · exact events
      · simpa only [Option.toList_none, List.append_nil] using deferred

theorem per_transaction_success_derives_checked_index_observations {O E T X : Type}
    (api : Api O E T) (keys : Keys) (codec : Codec) (index : Backend O E T)
    (body : Delta O E → Outcome O E X) (registryMatches exclusive : Bool)
    (transaction : T) (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (combinedApi api keys codec index body) registryMatches exclusive .perTransaction
      transaction parent queued = some committed) :
    ∃ height witness countValue,
      index.convert transaction = some witness.encoded ∧
      index.read ⟨parent, (body ⟨parent, empty⟩).cache⟩ (keys.identifier height witness.encoded.identifier) = some none ∧
      index.read ⟨parent, (body ⟨parent, empty⟩).cache⟩ (keys.count height) = some countValue ∧
      TransferIndexWriterModel01.countObservation codec countValue = some witness.ordinal ∧
      witness.next.val = witness.ordinal.val + 1 ∧ witness.ordinal.val + 1 < 2 ^ 64 ∧
      committed.parent = applyCache parent
        (TransferIndexWriterModel01.writeIndex keys codec height witness (body ⟨parent, empty⟩).cache) := by
  obtain ⟨_, _, height, witness, _, _, inspected, applied, _, _⟩ :=
    per_transaction_success_recovers_body_height_and_index api keys codec index body registryMatches exclusive
      transaction parent queued committed success
  obtain ⟨countValue, converted, absent, countRead, decoded, _⟩ := TransferIndexInspectionFacts01.inspect_success_order
    keys codec index height transaction ⟨parent, (body ⟨parent, empty⟩).cache⟩ witness inspected
  obtain ⟨increment, bound⟩ := TransferIndexInspectionFacts01.inspect_success_checked_increment
    keys codec index height transaction ⟨parent, (body ⟨parent, empty⟩).cache⟩ witness inspected
  exact ⟨height, witness, countValue, converted, absent, countRead, decoded, increment, bound, applied⟩

theorem per_transaction_success_preserves_body_effect_domains {O E T X : Type}
    (api : Api O E T) (keys : Keys) (codec : Codec) (index : Backend O E T)
    (body : Delta O E → Outcome O E X) (registryMatches exclusive : Bool)
    (transaction : T) (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (combinedApi api keys codec index body) registryMatches exclusive .perTransaction
      transaction parent queued = some committed) :
    committed.parent.verifiable = (applyCache parent (body ⟨parent, empty⟩).cache).verifiable ∧
      committed.parent.objects = (applyCache parent (body ⟨parent, empty⟩).cache).objects ∧
      committed.events = (body ⟨parent, empty⟩).cache.events ∧ committed.deferred = queued := by
  obtain ⟨_, _, _, _, _, _, _, applied, events, deferred⟩ :=
    per_transaction_success_recovers_body_height_and_index api keys codec index body registryMatches exclusive
      transaction parent queued committed success
  refine ⟨?_, ?_, events, deferred⟩
  · rw [applied]; rfl
  · rw [applied]; rfl

theorem bound_ordinary_per_transaction_success_derives_markers {O E K X Tree A T : Type}
    (api : Api O E T) (keys : Keys) (codec : Codec) (index : Backend O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T) (different : entryKey ≠ dayKey)
    (success : run (combinedApi api keys codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item))
      registryMatches exclusive .perTransaction transaction parent queued = some committed) :
    extract action .ordinary = .ok item ∧ parent.verifiable entryKey = none ∧
      committed.parent.verifiable entryKey = some [1] ∧ committed.parent.verifiable dayKey = some [1] ∧
      committed.deferred = queued := by
  obtain ⟨_, _, _, _, bodySuccess, _, _, _, _, deferred⟩ :=
    per_transaction_success_recovers_body_height_and_index api keys codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item)
      registryMatches exclusive transaction parent queued committed success
  have derived := TransferBoundOrdinarySource01.successful_body_derives_reextraction_freshness_and_markers
    raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload
    nullifierKey entryKey dayKey action item ⟨parent, empty⟩ bodySuccess
  have markers := TransferBoundOrdinarySource01.successful_body_derives_visible_marker_values
    raw notes volume sct available extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload
    nullifierKey entryKey dayKey action item ⟨parent, empty⟩ different bodySuccess
  have frame := (per_transaction_success_preserves_body_effect_domains api keys codec index
    (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item)
    registryMatches exclusive transaction parent queued committed success).1
  refine ⟨derived.1, ?_, ?_, ?_, deferred⟩
  · simpa only [apply_empty] using derived.2.1
  · rw [frame]; exact markers.1
  · rw [frame]; exact markers.2

set_option pp.all true in
#check @combinedApi
#print axioms combinedApi
set_option pp.all true in
#check @selected_cache_derives_success
#print axioms selected_cache_derives_success
set_option pp.all true in
#check @per_transaction_success_recovers_body_height_and_index
#print axioms per_transaction_success_recovers_body_height_and_index
set_option pp.all true in
#check @per_transaction_success_derives_checked_index_observations
#print axioms per_transaction_success_derives_checked_index_observations
set_option pp.all true in
#check @per_transaction_success_preserves_body_effect_domains
#print axioms per_transaction_success_preserves_body_effect_domains
set_option pp.all true in
#check @bound_ordinary_per_transaction_success_derives_markers
#print axioms bound_ordinary_per_transaction_success_derives_markers

end ShielddSecurity.TransferOrdinaryIndexDelivery01
