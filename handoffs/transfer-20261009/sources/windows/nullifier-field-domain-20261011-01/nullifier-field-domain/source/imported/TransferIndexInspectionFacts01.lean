import ShielddSecurity.TransferIndexWriterModel01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferIndexInspectionFacts01

open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01

/-! Recover actual inspection observations and refine the same-height key tags.
The byte suffixes spell /count, /entry/ and /id/ from the pinned Rust helpers.
They are disjoint for arbitrary common prefixes and arbitrary appended values.
A projection into the earlier Nat-keyed cache must explicitly preserve equality.
This is a representation interface, not a cryptographic hash collision premise.
No target cache or successful callback observation is assumed as a conclusion. -/

def countBytes (prefixBytes : Bytes) : Bytes :=
  prefixBytes ++ [47, 99, 111, 117, 110, 116]

def entryBytes (prefixBytes ordinalBytes : Bytes) : Bytes :=
  prefixBytes ++ (47 :: 101 :: 110 :: 116 :: 114 :: 121 :: 47 :: ordinalBytes)

def identifierBytes (prefixBytes identifier : Bytes) : Bytes :=
  prefixBytes ++ (47 :: 105 :: 100 :: 47 :: identifier)

def keysFromBytes (project : Bytes → Nat) (prefixBytes : Nat → Bytes)
    (ordinalBytes : Nat → Bytes) : Keys :=
  ⟨fun height ordinal => project (entryBytes (prefixBytes height) (ordinalBytes ordinal)),
   fun height identifier => project (identifierBytes (prefixBytes height) identifier),
   fun height => project (countBytes (prefixBytes height))⟩

theorem inspect_success_order {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (witness : Witness) (success : inspect keys codec backend height transaction child = .ok witness) :
    ∃ countValue,
      backend.convert transaction = some witness.encoded ∧
      backend.read child (keys.identifier height witness.encoded.identifier) = some none ∧
      backend.read child (keys.count height) = some countValue ∧
      countObservation codec countValue = some witness.ordinal ∧
      nextOrdinal witness.ordinal = some witness.next := by
  cases converted : backend.convert transaction with
  | none => simp only [inspect, converted] at success; contradiction
  | some encoded =>
    cases idRead : backend.read child (keys.identifier height encoded.identifier) with
    | none => simp only [inspect, converted, idRead] at success; contradiction
    | some idValue =>
      cases idValue with
      | some previous => simp only [inspect, converted, idRead] at success; contradiction
      | none =>
        cases countRead : backend.read child (keys.count height) with
        | none => simp only [inspect, converted, idRead, countRead] at success; contradiction
        | some countValue =>
          cases decoded : countObservation codec countValue with
          | none => simp only [inspect, converted, idRead, countRead, decoded] at success; contradiction
          | some ordinal =>
            cases checked : nextOrdinal ordinal with
            | none => simp only [inspect, converted, idRead, countRead, decoded, checked] at success; contradiction
            | some next =>
              have same : (⟨encoded, ordinal, next⟩ : Witness) = witness :=
                Except.ok.inj (by simpa only [inspect, converted, idRead, countRead, decoded, checked] using success)
              subst witness
              exact ⟨countValue, rfl, idRead, rfl, decoded, checked⟩

theorem inspect_success_checked_increment {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (witness : Witness) (success : inspect keys codec backend height transaction child = .ok witness) :
    witness.next.val = witness.ordinal.val + 1 ∧ witness.ordinal.val + 1 < 2 ^ 64 := by
  obtain ⟨_, _, _, _, _, checked⟩ := inspect_success_order keys codec backend height transaction child witness success
  have increment := nextOrdinal_success witness.ordinal witness.next checked
  exact ⟨increment, by rw [← increment]; exact witness.next.isLt⟩

theorem count_entry_separate (prefixBytes ordinalBytes : Bytes) :
    countBytes prefixBytes ≠ entryBytes prefixBytes ordinalBytes := by
  intro equal
  have suffix := (List.append_right_inj prefixBytes).mp equal
  have impossible : (99 : Nat) = 101 := (List.cons.inj (List.cons.inj suffix).2).1
  contradiction

theorem count_identifier_separate (prefixBytes identifier : Bytes) :
    countBytes prefixBytes ≠ identifierBytes prefixBytes identifier := by
  intro equal
  have suffix := (List.append_right_inj prefixBytes).mp equal
  have impossible : (99 : Nat) = 105 := (List.cons.inj (List.cons.inj suffix).2).1
  contradiction

theorem entry_identifier_separate (prefixBytes ordinalBytes identifier : Bytes) :
    entryBytes prefixBytes ordinalBytes ≠ identifierBytes prefixBytes identifier := by
  intro equal
  have suffix := (List.append_right_inj prefixBytes).mp equal
  have impossible : (101 : Nat) = 105 := (List.cons.inj (List.cons.inj suffix).2).1
  contradiction

theorem projected_keys_separate (project : Bytes → Nat)
    (injection : Function.Injective project) (prefixBytes : Nat → Bytes)
    (ordinalBytes : Nat → Bytes) (height ordinal : Nat) (identifier : Bytes) :
    let keys := keysFromBytes project prefixBytes ordinalBytes
    keys.entry height ordinal ≠ keys.count height ∧
    keys.identifier height identifier ≠ keys.count height ∧
    keys.entry height ordinal ≠ keys.identifier height identifier := by
  refine ⟨?_, ?_, ?_⟩
  · intro equal
    exact count_entry_separate (prefixBytes height) (ordinalBytes ordinal) (injection equal).symm
  · intro equal
    exact count_identifier_separate (prefixBytes height) identifier (injection equal).symm
  · intro equal
    exact entry_identifier_separate (prefixBytes height) (ordinalBytes ordinal) identifier (injection equal)

theorem writeIndex_entry {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (cache : Cache O E)
    (countDifferent : keys.entry height witness.ordinal.val ≠ keys.count height)
    (idDifferent : keys.entry height witness.ordinal.val ≠ keys.identifier height witness.encoded.identifier) :
    (writeIndex keys codec height witness cache).nonverifiable (keys.entry height witness.ordinal.val) =
      some (some witness.encoded.payload) := by
  simp only [writeIndex, putNV, if_neg countDifferent, if_neg idDifferent, ite_true]

theorem writeIndex_identifier {O E : Type} (keys : Keys) (codec : Codec) (height : Nat)
    (witness : Witness) (cache : Cache O E)
    (countDifferent : keys.identifier height witness.encoded.identifier ≠ keys.count height) :
    (writeIndex keys codec height witness cache).nonverifiable (keys.identifier height witness.encoded.identifier) =
      some (some (codec.encodeCount witness.ordinal)) := by
  simp only [writeIndex, putNV, if_neg countDifferent, ite_true]

theorem successful_index_exact_values {O E T : Type} (project : Bytes → Nat)
    (injection : Function.Injective project) (prefixBytes : Nat → Bytes)
    (ordinalBytes : Nat → Bytes) (codec : Codec) (backend : Backend O E T)
    (height : Nat) (transaction : T) (child : Delta O E) (indexed : Cache O E)
    (success : asCache (executeIndex (keysFromBytes project prefixBytes ordinalBytes)
      codec backend height transaction child) = some indexed) :
    let keys := keysFromBytes project prefixBytes ordinalBytes
    ∃ witness countValue,
      backend.convert transaction = some witness.encoded ∧
      backend.read child (keys.identifier height witness.encoded.identifier) = some none ∧
      backend.read child (keys.count height) = some countValue ∧
      countObservation codec countValue = some witness.ordinal ∧
      witness.next.val = witness.ordinal.val + 1 ∧ witness.ordinal.val + 1 < 2 ^ 64 ∧
      indexed = writeIndex keys codec height witness child.cache ∧
      indexed.nonverifiable (keys.entry height witness.ordinal.val) = some (some witness.encoded.payload) ∧
      indexed.nonverifiable (keys.identifier height witness.encoded.identifier) = some (some (codec.encodeCount witness.ordinal)) ∧
      indexed.nonverifiable (keys.count height) = some (some (codec.encodeCount witness.next)) := by
  obtain ⟨witness, observed, same⟩ := successful_index_writes
    (keysFromBytes project prefixBytes ordinalBytes) codec backend height transaction child indexed success
  obtain ⟨countValue, converted, absent, countRead, decoded, _⟩ := inspect_success_order
    (keysFromBytes project prefixBytes ordinalBytes) codec backend height transaction child witness observed
  obtain ⟨increment, bound⟩ := inspect_success_checked_increment
    (keysFromBytes project prefixBytes ordinalBytes) codec backend height transaction child witness observed
  obtain ⟨entryCount, idCount, entryId⟩ := projected_keys_separate project injection prefixBytes
    ordinalBytes height witness.ordinal.val witness.encoded.identifier
  refine ⟨witness, countValue, converted, absent, countRead, decoded, increment, bound, same, ?_, ?_, ?_⟩
  · rw [same]
    exact writeIndex_entry _ codec height witness child.cache entryCount entryId
  · rw [same]
    exact writeIndex_identifier _ codec height witness child.cache idCount
  · rw [same]
    exact writeIndex_count _ codec height witness child.cache

theorem index_conversion_refusal {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (rejected : backend.convert transaction = none) :
    inspect keys codec backend height transaction child = .error .conversion := by
  simp only [inspect, rejected]

theorem index_duplicate_refusal {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (encoded : Encoded) (previous : Bytes)
    (converted : backend.convert transaction = some encoded)
    (duplicate : backend.read child (keys.identifier height encoded.identifier) = some (some previous)) :
    inspect keys codec backend height transaction child = .error .duplicate := by
  simp only [inspect, converted, duplicate]

theorem index_overflow_refusal {O E T : Type} (keys : Keys) (codec : Codec)
    (backend : Backend O E T) (height : Nat) (transaction : T) (child : Delta O E)
    (encoded : Encoded) (countValue : Option Bytes) (ordinal : Ordinal)
    (converted : backend.convert transaction = some encoded)
    (absent : backend.read child (keys.identifier height encoded.identifier) = some none)
    (countRead : backend.read child (keys.count height) = some countValue)
    (decoded : countObservation codec countValue = some ordinal)
    (overflow : 2 ^ 64 ≤ ordinal.val + 1) :
    inspect keys codec backend height transaction child = .error .overflow := by
  simp only [inspect, converted, absent, countRead, decoded, nextOrdinal_overflow ordinal overflow]

set_option pp.all true in
#check @countBytes
#print axioms countBytes
set_option pp.all true in
#check @entryBytes
#print axioms entryBytes
set_option pp.all true in
#check @identifierBytes
#print axioms identifierBytes
set_option pp.all true in
#check @keysFromBytes
#print axioms keysFromBytes
set_option pp.all true in
#check @inspect_success_order
#print axioms inspect_success_order
set_option pp.all true in
#check @inspect_success_checked_increment
#print axioms inspect_success_checked_increment
set_option pp.all true in
#check @count_entry_separate
#print axioms count_entry_separate
set_option pp.all true in
#check @count_identifier_separate
#print axioms count_identifier_separate
set_option pp.all true in
#check @entry_identifier_separate
#print axioms entry_identifier_separate
set_option pp.all true in
#check @projected_keys_separate
#print axioms projected_keys_separate
set_option pp.all true in
#check @writeIndex_entry
#print axioms writeIndex_entry
set_option pp.all true in
#check @writeIndex_identifier
#print axioms writeIndex_identifier
set_option pp.all true in
#check @successful_index_exact_values
#print axioms successful_index_exact_values
set_option pp.all true in
#check @index_conversion_refusal
#print axioms index_conversion_refusal
set_option pp.all true in
#check @index_duplicate_refusal
#print axioms index_duplicate_refusal
set_option pp.all true in
#check @index_overflow_refusal
#print axioms index_overflow_refusal

end ShielddSecurity.TransferIndexInspectionFacts01
