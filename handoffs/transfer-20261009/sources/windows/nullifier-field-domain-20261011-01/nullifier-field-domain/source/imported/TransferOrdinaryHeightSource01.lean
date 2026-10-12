import ShielddSecurity.TransferOrdinaryIndexedValues01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOrdinaryHeightSource01

open TransferStateDelta TransferRawStateProgram01
open TransferIndexWriterModel01 (Keys Codec Backend Witness)
open TransferVerificationEqualitySource01 (Item)

/-! Model get_block_height's current verifiable read and decode. Missing,
unavailable or undecodable data cannot produce a successful height. Ordinary
body V framing preserves every key outside its two volume markers, including
the height key under explicit representation separation. Whole indexed success
therefore derives an original parent height value and decoder observation.
Actual Rust get_proto/codec/key/store correspondence remains an interface. -/

def readHeight {O E : Type} (available : Delta O E → Bool) (decode : Bytes → Option Nat)
    (heightKey : Nat) (child : Delta O E) : Option Nat :=
  if available child then ((applyCache child.parent child.cache).verifiable heightKey).bind decode else none

def withHeight {O E T : Type} (api : Api O E T) (available : Delta O E → Bool)
    (decode : Bytes → Option Nat) (heightKey : Nat) : Api O E T :=
  {api with height := readHeight available decode heightKey}

theorem successful_height_derives_actual_read_and_decode {O E : Type}
    (available : Delta O E → Bool) (decode : Bytes → Option Nat) (heightKey height : Nat)
    (child : Delta O E) (success : readHeight available decode heightKey child = some height) :
    available child = true ∧ ∃ bytes,
      (applyCache child.parent child.cache).verifiable heightKey = some bytes ∧ decode bytes = some height := by
  cases readable : available child with
  | false => simp [readHeight, readable] at success
  | true =>
    cases present : (applyCache child.parent child.cache).verifiable heightKey with
    | none => simp [readHeight, readable, present] at success
    | some bytes =>
      refine ⟨rfl, bytes, rfl, ?_⟩
      simpa only [readHeight, readable, ↓reduceIte, present, Option.bind_some] using success

theorem bound_body_preserves_every_other_verifiable_key {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey other : Nat)
    (action : A) (item : Item) (child : Delta O E) (notEntry : other ≠ entryKey) (notDay : other ≠ dayKey) :
    (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item child).cache.verifiable other =
        child.cache.verifiable other := by
  cases observed : extract action .ordinary with
  | error error => simp only [TransferBoundOrdinarySource01.executeBound, TransferCapabilitySource01.execute, observed]
  | ok current =>
    by_cases matched : current = item
    · simp only [TransferBoundOrdinarySource01.executeBound, TransferCapabilitySource01.execute, observed,
        if_pos matched, TransferCapabilitySource01.liftRaw, TransferCapabilitySource01.isOrdinary]
      change (TransferOrdinaryStorageSource01.execute raw notes volume sct available wordMax capacity treeKey notesKey
        volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)).cache.verifiable other = _
      have frames := (TransferOrdinaryStorageSource01.execution_preserves_nv_and_only_adds_volume_markers raw notes volume sct available
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey true child (inputs action) (outputs action)).2
      rcases frames with unchanged | marked
      · rw [unchanged]
      · rw [marked]
        simp only [TransferRawEffectsSource01.putV, if_neg notDay, if_neg notEntry]
    · simp only [TransferBoundOrdinarySource01.executeBound, TransferCapabilitySource01.execute, observed, if_neg matched]

theorem whole_indexed_success_derives_original_parent_height {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (codec : Codec) (index : Backend O E A)
    (heightAvailable volumeAvailable : Delta O E → Bool) (decode : Bytes → Option Nat)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey heightKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O)
    (queued : List A) (committed : Commit O E A) (notEntry : heightKey ≠ entryKey) (notDay : heightKey ≠ dayKey)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi
      (withHeight api heightAvailable decode heightKey) keys codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item))
      registryMatches exclusive .perTransaction action parent queued = some committed) :
    ∃ (height : Nat) (bytes : Bytes) (witness : Witness),
      parent.verifiable heightKey = some bytes ∧ decode bytes = some height ∧
      heightAvailable ⟨parent, (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item ⟨parent, empty⟩).cache⟩ = true ∧
      TransferIndexWriterModel01.inspect keys codec index height action
        ⟨parent, (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs
          wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item ⟨parent, empty⟩).cache⟩ = .ok witness ∧
      committed.parent.verifiable heightKey = some bytes := by
  obtain ⟨_, _, height, witness, _, heightRead, inspected, _, _, _⟩ :=
    TransferOrdinaryIndexDelivery01.per_transaction_success_recovers_body_height_and_index
      (withHeight api heightAvailable decode heightKey) keys codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item)
      registryMatches exclusive action parent queued committed success
  obtain ⟨readable, bytes, present, decoded⟩ := successful_height_derives_actual_read_and_decode heightAvailable decode heightKey height _ heightRead
  have bodyFrame := bound_body_preserves_every_other_verifiable_key raw notes volume sct volumeAvailable extract inputs outputs
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey heightKey action item ⟨parent, empty⟩ notEntry notDay
  have visible := present
  have original : parent.verifiable heightKey = some bytes := by
    change overlay parent.verifiable _ heightKey = some bytes at present
    simp only [overlay] at present
    rw [bodyFrame] at present
    exact present
  have finalFrame := (TransferOrdinaryIndexDelivery01.per_transaction_success_preserves_body_effect_domains
    (withHeight api heightAvailable decode heightKey) keys codec index
    (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item)
    registryMatches exclusive action parent queued committed success).1
  refine ⟨height, bytes, witness, original, decoded, readable, inspected, ?_⟩
  rw [finalFrame]
  exact visible

set_option pp.all true in
#check @readHeight
#print axioms readHeight
set_option pp.all true in
#check @withHeight
#print axioms withHeight
set_option pp.all true in
#check @successful_height_derives_actual_read_and_decode
#print axioms successful_height_derives_actual_read_and_decode
set_option pp.all true in
#check @bound_body_preserves_every_other_verifiable_key
#print axioms bound_body_preserves_every_other_verifiable_key
set_option pp.all true in
#check @whole_indexed_success_derives_original_parent_height
#print axioms whole_indexed_success_derives_original_parent_height

end ShielddSecurity.TransferOrdinaryHeightSource01
