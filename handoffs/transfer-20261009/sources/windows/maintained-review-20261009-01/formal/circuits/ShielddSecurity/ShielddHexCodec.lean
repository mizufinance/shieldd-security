import ShielddSecurity.GroupByteCodec

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexCodec

open GroupByteCodec

/- Source view of hex0.4.3's ASCII table and val. Error payloads and character
indices are erased to None; byte values, success/failure and their order are
retained. Natural arithmetic models u8 shift/mask operations on bounded
nibbles. Their exact Rust operational correspondence is separately audited. -/
def lowerDigit (nibble : Nat) : Nat :=
  if nibble < 10 then 48 + nibble else 87 + nibble

def value (ascii : Nat) : Option Nat :=
  if 65 ≤ ascii ∧ ascii ≤ 70 then some (ascii - 65 + 10)
  else if 97 ≤ ascii ∧ ascii ≤ 102 then some (ascii - 97 + 10)
  else if 48 ≤ ascii ∧ ascii ≤ 57 then some (ascii - 48)
  else none

theorem lower_digit_value (nibble : Nat) (bounded : nibble < 16) :
    value (lowerDigit nibble) = some nibble := by
  by_cases decimal : nibble < 10
  · have upper : ¬ (65 ≤ 48 + nibble ∧ 48 + nibble ≤ 70) := by omega
    have lower : ¬ (97 ≤ 48 + nibble ∧ 48 + nibble ≤ 102) := by omega
    have digit : 48 ≤ 48 + nibble ∧ 48 + nibble ≤ 57 := by omega
    simp only [lowerDigit, if_pos decimal, value, if_neg upper, if_neg lower, if_pos digit]
    congr 1
    omega
  · have upper : ¬ (65 ≤ 87 + nibble ∧ 87 + nibble ≤ 70) := by omega
    have lower : 97 ≤ 87 + nibble ∧ 87 + nibble ≤ 102 := by omega
    simp only [lowerDigit, if_neg decimal, value, if_neg upper, if_pos lower]
    congr 1
    omega

theorem value_bounded (ascii nibble : Nat) (decoded : value ascii = some nibble) :
    nibble < 16 := by
  unfold value at decoded
  split_ifs at decoded with upper lower digit
  · have same := Option.some.inj decoded
    omega
  · have same := Option.some.inj decoded
    omega
  · have same := Option.some.inj decoded
    omega

def decodePair (high low : Nat) : Option Byte := do
  let h ← value high
  let l ← value low
  if bounded : 16 * h + l < 256 then some ⟨16 * h + l, bounded⟩ else none

theorem byte_pair_decode (byte : Byte) :
    decodePair (lowerDigit (byte.val / 16)) (lowerDigit (byte.val % 16)) = some byte := by
  have high : byte.val / 16 < 16 := by have := byte.isLt; omega
  have low : byte.val % 16 < 16 := Nat.mod_lt _ (by decide)
  have restored : 16 * (byte.val / 16) + byte.val % 16 = byte.val := by omega
  have bounded : 16 * (byte.val / 16) + byte.val % 16 < 256 := by
    rw [restored]
    exact byte.isLt
  unfold decodePair
  rw [lower_digit_value _ high, lower_digit_value _ low]
  change (if valid : 16 * (byte.val / 16) + byte.val % 16 < 256 then
    some (⟨16 * (byte.val / 16) + byte.val % 16, valid⟩ : Byte) else none) = some byte
  rw [dif_pos bounded]
  apply congrArg Option.some
  exact Fin.ext restored

def encode : List Byte → List Nat
  | [] => []
  | byte :: rest => lowerDigit (byte.val / 16) :: lowerDigit (byte.val % 16) :: encode rest

theorem encode_length (bytes : List Byte) : (encode bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih => simp only [encode, List.length_cons, ih]; omega

/- Exact pending-character state of BytesToHexChars::next: consume a byte and
emit its high digit, then take the saved low digit without consuming a byte. -/
structure IteratorState where
  unread : List Byte
  pending : Option Nat

def next (state : IteratorState) : Option (Nat × IteratorState) :=
  match state.pending with
  | some current => some (current, ⟨state.unread, none⟩)
  | none => match state.unread with
    | [] => none
    | byte :: rest => some (lowerDigit (byte.val / 16),
        ⟨rest, some (lowerDigit (byte.val % 16))⟩)

theorem iterator_byte_pair (byte : Byte) (rest : List Byte) :
    next ⟨byte :: rest, none⟩ =
      some (lowerDigit (byte.val / 16), ⟨rest, some (lowerDigit (byte.val % 16))⟩) ∧
    next ⟨rest, some (lowerDigit (byte.val % 16))⟩ =
      some (lowerDigit (byte.val % 16), ⟨rest, none⟩) := ⟨rfl, rfl⟩

def drain : Nat → IteratorState → List Nat
  | 0, _ => []
  | fuel + 1, state => match next state with
    | none => []
    | some (ascii, remaining) => ascii :: drain fuel remaining

theorem iterator_encode (bytes : List Byte) :
    drain (2 * bytes.length) ⟨bytes, none⟩ = encode bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have fuel : 2 * (byte :: rest).length = 2 * rest.length + 2 := by
      simp only [List.length_cons]; omega
    rw [fuel]
    change lowerDigit (byte.val / 16) :: lowerDigit (byte.val % 16) ::
      drain (2 * rest.length) ⟨rest, none⟩ =
      lowerDigit (byte.val / 16) :: lowerDigit (byte.val % 16) :: encode rest
    rw [ih]

def advance : Nat → IteratorState → IteratorState
  | 0, state => state
  | fuel + 1, state => match next state with
    | none => state
    | some (_, remaining) => advance fuel remaining

theorem iterator_exhausted (bytes : List Byte) :
    advance (2 * bytes.length) ⟨bytes, none⟩ = ⟨[], none⟩ := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have fuel : 2 * (byte :: rest).length = 2 * rest.length + 2 := by
      simp only [List.length_cons]; omega
    rw [fuel]
    change advance (2 * rest.length) ⟨rest, none⟩ = ⟨[], none⟩
    exact ih

/- Vec::from_hex rejects odd input first, then chunks2/map/collect evaluates
the same ordered pair recurrence, propagating the first rejected pair. -/
def decodePairs : List Nat → Option (List Byte)
  | [] => some []
  | [_] => none
  | high :: low :: rest => do
    let byte ← decodePair high low
    let bytes ← decodePairs rest
    some (byte :: bytes)

def decode (ascii : List Nat) : Option (List Byte) :=
  if ascii.length % 2 = 0 then decodePairs ascii else none

theorem decode_pairs_encoded (bytes : List Byte) : decodePairs (encode bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    change (decodePair (lowerDigit (byte.val / 16)) (lowerDigit (byte.val % 16))).bind
      (fun value => (decodePairs (encode rest)).bind (fun remaining => some (value :: remaining))) = _
    rw [byte_pair_decode]
    change (decodePairs (encode rest)).bind (fun remaining => some (byte :: remaining)) = _
    rw [ih]
    rfl

theorem decode_encoded (bytes : List Byte) : decode (encode bytes) = some bytes := by
  have even : (encode bytes).length % 2 = 0 := by rw [encode_length]; omega
  simp only [decode, if_pos even]
  exact decode_pairs_encoded bytes

theorem odd_rejected (ascii : List Nat) (odd : ascii.length % 2 ≠ 0) :
    decode ascii = none := by simp only [decode, if_neg odd]

set_option pp.all true in
#check @lower_digit_value
#print axioms lower_digit_value
set_option pp.all true in
#check @value_bounded
#print axioms value_bounded
set_option pp.all true in
#check @byte_pair_decode
#print axioms byte_pair_decode
set_option pp.all true in
#check @encode_length
#print axioms encode_length
set_option pp.all true in
#check @iterator_byte_pair
#print axioms iterator_byte_pair
set_option pp.all true in
#check @iterator_encode
#print axioms iterator_encode
set_option pp.all true in
#check @iterator_exhausted
#print axioms iterator_exhausted
set_option pp.all true in
#check @decode_pairs_encoded
#print axioms decode_pairs_encoded
set_option pp.all true in
#check @decode_encoded
#print axioms decode_encoded
set_option pp.all true in
#check @odd_rejected
#print axioms odd_rejected

end ShielddSecurity.ShielddHexCodec
