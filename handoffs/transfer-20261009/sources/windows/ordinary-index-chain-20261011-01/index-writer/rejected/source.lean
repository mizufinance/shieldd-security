import ShielddSecurity.TransferRawDeliveryComposition01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferIndexWriterModel01

open TransferStateDelta TransferRawStateProgram01 TransferRawDeliveryComposition01

/-! Source-order model of put_block_transaction at the exact runtime lock.
All fallible observations precede exactly three nonverifiable writes. Conversion,
key projection, big-endian codecs and storage observations remain interfaces.
The write primitive is explicit; it cannot replace earlier verifiable, object or
event effects. Nat keys stand for projected byte keys, whose identity/framing
correspondence to Rust is separate. No semantic claim follows from source hashes. -/

abbrev Ordinal := Fin (2 ^ 64)

inductive IndexError where
  | conversion | idRead | duplicate | countRead | countDecode | overflow

structure Keys where
  entry : Nat → Nat → Nat
  identifier : Nat → Bytes → Nat
  count : Nat → Nat

structure Encoded where
  identifier : Bytes
  payload : Bytes

structure Codec where
  decodeCount : Bytes → Option Ordinal
  encodeCount : Ordinal → Bytes

structure Backend (O E T : Type) where
  convert : T → Option Encoded
  read : Delta O E → Nat → Option (Option Bytes)

structure Witness where
  encoded : Encoded
  ordinal : Ordinal
  next : Ordinal

def putNV {O E : Type} (cache : Cache O E) (key : Nat) (value : Bytes) : Cache O E :=
  {cache with nonverifiable := fun other =>
    if other = key then some (some value) else cache.nonverifiable other}

def writeIndex {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (cache : Cache O E) : Cache O E :=
  putNV (putNV (putNV cache
    (keys.entry height witness.ordinal.val) witness.encoded.payload)
    (keys.identifier height witness.encoded.identifier) (codec.encodeCount witness.ordinal))
    (keys.count height) (codec.encodeCount witness.next)

def countObservation (codec : Codec) (bytes : Option Bytes) : Option Ordinal :=
  match bytes with
  | none => some ⟨0, by decide⟩
  | some value => codec.decodeCount value

def nextOrdinal (ordinal : Ordinal) : Option Ordinal :=
  if bound : ordinal.val + 1 < 2 ^ 64 then some ⟨ordinal.val + 1, bound⟩ else none

def inspect {O E T : Type} (keys : Keys) (codec : Codec) (backend : Backend O E T)
    (height : Nat) (transaction : T) (child : Delta O E) : Except IndexError Witness :=
  match backend.convert transaction with
  | none => .error .conversion
  | some encoded =>
    match backend.read child (keys.identifier height encoded.identifier) with
    | none => .error .idRead
    | some (some _) => .error .duplicate
    | some none =>
      match backend.read child (keys.count height) with
      | none => .error .countRead
      | some countBytes =>
        match countObservation codec countBytes with
        | none => .error .countDecode
        | some ordinal =>
          match nextOrdinal ordinal with
          | none => .error .overflow
          | some next => .ok ⟨encoded, ordinal, next⟩

def executeIndex {O E T : Type} (keys : Keys) (codec : Codec) (backend : Backend O E T)
    (height : Nat) (transaction : T) (child : Delta O E) : Outcome O E IndexError :=
  match inspect keys codec backend height transaction child with
  | .error error => ⟨child.cache, .error error⟩
  | .ok witness => ⟨writeIndex keys codec height witness child.cache, .ok ()⟩

def indexApi {O E T : Type} (api : Api O E T) (keys : Keys) (codec : Codec)
    (backend : Backend O E T) : Api O E T :=
  {api with index := fun height transaction child =>
    asCache (executeIndex keys codec backend height transaction child)}

theorem nextOrdinal_success (ordinal next : Ordinal)
    (success : nextOrdinal ordinal = some next) : next.val = ordinal.val + 1 := by
  unfold nextOrdinal at success
  split at success
  next bound =>
    have same := Option.some.inj success
    exact congrArg Fin.val same.symm
  next bound => simp at success

theorem nextOrdinal_overflow (ordinal : Ordinal)
    (overflow : 2 ^ 64 ≤ ordinal.val + 1) : nextOrdinal ordinal = none := by
  simp only [nextOrdinal, dif_neg (Nat.not_lt.mpr overflow)]

theorem absent_count_zero (codec : Codec) :
    countObservation codec none = some ⟨0, by decide⟩ := rfl

theorem putNV_frames {O E : Type} (cache : Cache O E) (key : Nat) (value : Bytes) :
    (putNV cache key value).verifiable = cache.verifiable ∧
    (putNV cache key value).objects = cache.objects ∧
    (putNV cache key value).events = cache.events := ⟨rfl, rfl, rfl⟩

theorem writeIndex_frames {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (cache : Cache O E) :
    (writeIndex keys codec height witness cache).verifiable = cache.verifiable ∧
    (writeIndex keys codec height witness cache).objects = cache.objects ∧
    (writeIndex keys codec height witness cache).events = cache.events := ⟨rfl, rfl, rfl⟩

theorem writeIndex_unrelated {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (cache : Cache O E) (other : Nat)
    (entryDifferent : other ≠ keys.entry height witness.ordinal.val)
    (idDifferent : other ≠ keys.identifier height witness.encoded.identifier)
    (countDifferent : other ≠ keys.count height) :
    (writeIndex keys codec height witness cache).nonverifiable other = cache.nonverifiable other := by
  simp only [writeIndex, putNV, if_neg entryDifferent, if_neg idDifferent, if_neg countDifferent]

theorem writeIndex_count {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (cache : Cache O E) :
    (writeIndex keys codec height witness cache).nonverifiable (keys.count height) =
      some (some (codec.encodeCount witness.next)) := by
  simp only [writeIndex, putNV, if_pos rfl]

theorem apply_index_unrelated {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (parent : State O) (cache : Cache O E) (other : Nat)
    (entryDifferent : other ≠ keys.entry height witness.ordinal.val)
    (idDifferent : other ≠ keys.identifier height witness.encoded.identifier)
    (countDifferent : other ≠ keys.count height) :
    (applyCache parent (writeIndex keys codec height witness cache)).nonverifiable other =
      (applyCache parent cache).nonverifiable other := by
  simp only [applyCache, overlay]
  rw [writeIndex_unrelated keys codec height witness cache other entryDifferent idDifferent countDifferent]

theorem inspection_error_retains_cache {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (error : IndexError) (rejected : inspect keys codec backend height transaction child = .error error) :
    executeIndex keys codec backend height transaction child = ⟨child.cache, .error error⟩ := by
  simp only [executeIndex, rejected]

theorem inspection_error_refuses_index {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (error : IndexError) (rejected : inspect keys codec backend height transaction child = .error error) :
    asCache (executeIndex keys codec backend height transaction child) = none := by
  rw [inspection_error_retains_cache keys codec backend height transaction child error rejected]
  rfl

theorem successful_index_writes {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (indexed : Cache O E)
    (success : asCache (executeIndex keys codec backend height transaction child) = some indexed) :
    ∃ witness, inspect keys codec backend height transaction child = .ok witness ∧
      indexed = writeIndex keys codec height witness child.cache := by
  cases observed : inspect keys codec backend height transaction child with
  | error error => simp only [executeIndex, observed, asCache] at success; contradiction
  | ok witness =>
    have same : writeIndex keys codec height witness child.cache = indexed :=
      Option.some.inj (by simpa only [executeIndex, observed, asCache] using success)
    exact ⟨witness, observed, same.symm⟩

theorem raw_per_transaction_preserves_effects {O E T A X : Type} (api : Api O E T)
    (keys : Keys) (codec : Codec) (backend : Backend O E T)
    (steps : State O → Step O E A X) (commands : List A)
    (registryMatches exclusive : Bool) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (executionApi (indexApi api keys codec backend) steps commands)
      registryMatches exclusive .perTransaction transaction parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧
      ∃ cache height witness,
        walk (steps parent) empty commands = ⟨cache, .ok ()⟩ ∧
        api.height ⟨parent, cache⟩ = some height ∧
        inspect keys codec backend height transaction ⟨parent, cache⟩ = .ok witness ∧
        committed.parent = applyCache parent (writeIndex keys codec height witness cache) ∧
        committed.parent.verifiable = (applyCache parent cache).verifiable ∧
        committed.parent.objects = (applyCache parent cache).objects ∧
        committed.events = cache.events ∧ committed.deferred = queued ∧
        ∀ other, other ≠ keys.entry height witness.ordinal.val →
          other ≠ keys.identifier height witness.encoded.identifier →
          other ≠ keys.count height →
          committed.parent.nonverifiable other = (applyCache parent cache).nonverifiable other := by
  obtain ⟨registry, unique, cache, height, indexed, raw, observedHeight, observedIndex,
    applied, events, deferred⟩ := successful_raw_per_transaction_exact
      (indexApi api keys codec backend) steps commands registryMatches exclusive
      transaction parent queued committed success
  obtain ⟨witness, inspected, same⟩ := successful_index_writes keys codec backend height
    transaction ⟨parent, cache⟩ indexed observedIndex
  subst indexed
  refine ⟨registry, unique, cache, height, witness, raw, observedHeight, inspected,
    applied, ?_, ?_, ?_, deferred, ?_⟩
  · rw [applied]; rfl
  · rw [applied]; rfl
  · rw [events]; rfl
  · intro other entryDifferent idDifferent countDifferent
    rw [applied]
    exact apply_index_unrelated keys codec height witness parent cache other
      entryDifferent idDifferent countDifferent

set_option pp.all true in
#check @Ordinal
#print axioms Ordinal
set_option pp.all true in
#check @IndexError
#print axioms IndexError
set_option pp.all true in
#check @Keys
#print axioms Keys
set_option pp.all true in
#check @Encoded
#print axioms Encoded
set_option pp.all true in
#check @Codec
#print axioms Codec
set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @Witness
#print axioms Witness
set_option pp.all true in
#check @putNV
#print axioms putNV
set_option pp.all true in
#check @writeIndex
#print axioms writeIndex
set_option pp.all true in
#check @countObservation
#print axioms countObservation
set_option pp.all true in
#check @nextOrdinal
#print axioms nextOrdinal
set_option pp.all true in
#check @inspect
#print axioms inspect
set_option pp.all true in
#check @executeIndex
#print axioms executeIndex
set_option pp.all true in
#check @indexApi
#print axioms indexApi
set_option pp.all true in
#check @nextOrdinal_success
#print axioms nextOrdinal_success
set_option pp.all true in
#check @nextOrdinal_overflow
#print axioms nextOrdinal_overflow
set_option pp.all true in
#check @absent_count_zero
#print axioms absent_count_zero
set_option pp.all true in
#check @putNV_frames
#print axioms putNV_frames
set_option pp.all true in
#check @writeIndex_frames
#print axioms writeIndex_frames
set_option pp.all true in
#check @writeIndex_unrelated
#print axioms writeIndex_unrelated
set_option pp.all true in
#check @writeIndex_count
#print axioms writeIndex_count
set_option pp.all true in
#check @apply_index_unrelated
#print axioms apply_index_unrelated
set_option pp.all true in
#check @inspection_error_retains_cache
#print axioms inspection_error_retains_cache
set_option pp.all true in
#check @inspection_error_refuses_index
#print axioms inspection_error_refuses_index
set_option pp.all true in
#check @successful_index_writes
#print axioms successful_index_writes
set_option pp.all true in
#check @raw_per_transaction_preserves_effects
#print axioms raw_per_transaction_preserves_effects

end ShielddSecurity.TransferIndexWriterModel01
