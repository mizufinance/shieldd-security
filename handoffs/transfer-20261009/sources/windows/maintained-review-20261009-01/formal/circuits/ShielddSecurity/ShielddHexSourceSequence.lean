import ShielddSecurity.ShielddHexCodec

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexSourceSequence

open GroupByteCodec

/- This source sequence retains Rust Result's ordered failure and the actual
FromHexError character/index payload, rather than assuming a decoder answer.
Its inputs are the byte-valued ASCII/UTF8 source view; invalid UTF8 bytes are
tested individually by val, as in hex::decode's AsRef<[u8]> interface. -/
inductive Error where
  | oddLength
  | invalidCharacter (position ascii : Nat)

def erase {A : Type} : Except Error A → Option A
  | .ok result => some result
  | .error _ => none

theorem erase_bind {A B : Type} (result : Except Error A)
    (next : A → Except Error B) :
    erase (result.bind next) = (erase result).bind (fun value => erase (next value)) := by
  cases result <;> rfl

def pairAt (position high low : Nat) : Except Error Byte :=
  match highRead : ShielddHexCodec.value high with
  | none => .error (.invalidCharacter (2 * position) high)
  | some h => match lowRead : ShielddHexCodec.value low with
    | none => .error (.invalidCharacter (2 * position + 1) low)
    | some l =>
      .ok ⟨16 * h + l, by
        have hb := ShielddHexCodec.value_bounded high h highRead
        have lb := ShielddHexCodec.value_bounded low l lowRead
        omega⟩

theorem pair_erasure (position high low : Nat) :
    erase (pairAt position high low) = ShielddHexCodec.decodePair high low := by
  unfold pairAt
  split
  · rename_i highRead
    simp [erase, ShielddHexCodec.decodePair, highRead]
  · rename_i h highRead
    split
    · rename_i lowRead
      simp [erase, ShielddHexCodec.decodePair, highRead, lowRead]
    · rename_i l lowRead
      have hb := ShielddHexCodec.value_bounded high h highRead
      have lb := ShielddHexCodec.value_bounded low l lowRead
      have bounded : 16 * h + l < 256 := by omega
      simp [erase, ShielddHexCodec.decodePair, highRead, lowRead, bounded]

def decodeLoop : Nat → List Nat → Except Error (List Byte)
  | _, [] => .ok []
  | _, [_] => .error .oddLength
  | position, high :: low :: rest => do
    let byte ← pairAt position high low
    let bytes ← decodeLoop (position + 1) rest
    .ok (byte :: bytes)

theorem loop_erasure : ∀ (ascii : List Nat) (position : Nat),
    erase (decodeLoop position ascii) = ShielddHexCodec.decodePairs ascii
  | [], _ => rfl
  | [_], _ => rfl
  | high :: low :: rest, position => by
    change erase ((pairAt position high low).bind (fun byte =>
      (decodeLoop (position + 1) rest).bind (fun bytes => .ok (byte :: bytes)))) =
      (ShielddHexCodec.decodePair high low).bind (fun byte =>
        (ShielddHexCodec.decodePairs rest).bind (fun bytes => some (byte :: bytes)))
    rw [erase_bind, pair_erasure]
    apply congrArg (fun continuation : Byte → Option (List Byte) =>
      (ShielddHexCodec.decodePair high low).bind continuation)
    funext byte
    rw [erase_bind, loop_erasure rest (position + 1)]
    rfl

def decode (ascii : List Nat) : Except Error (List Byte) :=
  if ascii.length % 2 = 0 then decodeLoop 0 ascii else .error .oddLength

theorem decoder_erasure (ascii : List Nat) :
    erase (decode ascii) = ShielddHexCodec.decode ascii := by
  by_cases even : ascii.length % 2 = 0
  · simp only [decode, ShielddHexCodec.decode, if_pos even, loop_erasure]
  · simp only [decode, ShielddHexCodec.decode, if_neg even, erase]

theorem roundtrip_result (bytes : List Byte) :
    decode (ShielddHexCodec.encode bytes) = .ok bytes := by
  have restored : erase (decode (ShielddHexCodec.encode bytes)) = some bytes := by
    rw [decoder_erasure, ShielddHexCodec.decode_encoded]
  cases result : decode (ShielddHexCodec.encode bytes) with
  | error reason =>
    have impossible : False := by simpa only [result, erase, reduceCtorEq] using restored
    exact False.elim impossible
  | ok found =>
    have same : found = bytes := by
      simpa only [result, erase, Option.some.injEq] using restored
    subst found
    rfl

theorem first_character_error (position high low : Nat)
    (bad : ShielddHexCodec.value high = none) :
    pairAt position high low = .error (.invalidCharacter (2 * position) high) := by
  unfold pairAt
  split
  · rfl
  · rename_i h highRead
    simp [bad] at highRead

theorem second_character_error (position high low h : Nat)
    (read : ShielddHexCodec.value high = some h)
    (bad : ShielddHexCodec.value low = none) :
    pairAt position high low = .error (.invalidCharacter (2 * position + 1) low) := by
  unfold pairAt
  split
  · rename_i highRead
    simp [read] at highRead
  · rename_i found highRead
    split
    · rfl
    · rename_i l lowRead
      simp [bad] at lowRead

theorem lower_digit_ascii (nibble : Nat) (bound : nibble < 16) :
    ShielddHexCodec.lowerDigit nibble < 128 := by
  unfold ShielddHexCodec.lowerDigit
  split <;> omega

theorem encode_ascii (bytes : List Byte) : ∀ ascii ∈ ShielddHexCodec.encode bytes, ascii < 128 := by
  induction bytes with
  | nil => intro ascii member; simp only [ShielddHexCodec.encode, List.not_mem_nil] at member
  | cons byte rest ih =>
    intro ascii member
    simp only [ShielddHexCodec.encode, List.mem_cons] at member
    rcases member with same | same | member
    · subst ascii
      apply lower_digit_ascii
      have := byte.isLt
      omega
    · subst ascii
      exact lower_digit_ascii _ (Nat.mod_lt _ (by decide))
    · exact ih ascii member

set_option pp.all true in
#check @erase_bind
#print axioms erase_bind
set_option pp.all true in
#check @pair_erasure
#print axioms pair_erasure
set_option pp.all true in
#check @loop_erasure
#print axioms loop_erasure
set_option pp.all true in
#check @decoder_erasure
#print axioms decoder_erasure
set_option pp.all true in
#check @roundtrip_result
#print axioms roundtrip_result
set_option pp.all true in
#check @first_character_error
#print axioms first_character_error
set_option pp.all true in
#check @second_character_error
#print axioms second_character_error
set_option pp.all true in
#check @lower_digit_ascii
#print axioms lower_digit_ascii
set_option pp.all true in
#check @encode_ascii
#print axioms encode_ascii

end ShielddSecurity.ShielddHexSourceSequence
