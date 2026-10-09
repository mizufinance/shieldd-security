import ShielddSecurity.ShielddHexSourceSequence

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexStringOperations

/- Source view of Rust 1.95's char byte writes and String::push/Extend order.
The byte-store recurrence models successful reserve/write/set_len operations;
it does not certify an allocator, pointer implementation, or Rust execution.
Only the ASCII branch is needed by the actual lowercase hex iterator. -/
def utf8 (code : Nat) : List Nat :=
  if code < 128 then [code % 256]
  else if code < 2048 then [192 + (code / 64 % 32), 128 + (code % 64)]
  else if code < 65536 then
    [224 + (code / 4096 % 16), 128 + (code / 64 % 64), 128 + (code % 64)]
  else [240 + (code / 262144 % 8), 128 + (code / 4096 % 64),
    128 + (code / 64 % 64), 128 + (code % 64)]

def push (buffer : List Nat) (code : Nat) : List Nat := buffer ++ utf8 code

def extend : List Nat → List Nat → List Nat
  | buffer, [] => buffer
  | buffer, code :: rest => extend (push buffer code) rest

theorem utf8_ascii (code : Nat) (ascii : code < 128) : utf8 code = [code] := by
  have byte : code < 256 := by omega
  simp only [utf8, if_pos ascii, Nat.mod_eq_of_lt byte]

theorem push_ascii (buffer : List Nat) (code : Nat) (ascii : code < 128) :
    push buffer code = buffer ++ [code] := by
  rw [push, utf8_ascii code ascii]

theorem extend_append (buffer codes : List Nat) :
    extend buffer codes = buffer ++ extend [] codes := by
  induction codes generalizing buffer with
  | nil => simp only [extend, List.append_nil]
  | cons code rest ih =>
    simp only [extend, push, List.nil_append]
    rw [ih (buffer ++ utf8 code), ih (utf8 code), List.append_assoc]

theorem extend_ascii (buffer codes : List Nat)
    (ascii : ∀ code ∈ codes, code < 128) : extend buffer codes = buffer ++ codes := by
  induction codes generalizing buffer with
  | nil => simp only [extend, List.append_nil]
  | cons code rest ih =>
    have head : code < 128 := ascii code (List.mem_cons_self)
    have tail : ∀ entry ∈ rest, entry < 128 := by
      intro entry member
      exact ascii entry (List.mem_cons_of_mem code member)
    rw [extend, push_ascii buffer code head, ih _ tail]
    simp only [List.append_assoc, List.singleton_append]

/- `String::from_iter` starts from an empty buffer, `Extend<char>` visits the
iterator in order, and both String/str AsRef<[u8]> expose its stored bytes. -/
def encodedString (bytes : List GroupByteCodec.Byte) : List Nat :=
  extend [] (ShielddHexCodec.encode bytes)

theorem hex_string_bytes (bytes : List GroupByteCodec.Byte) :
    encodedString bytes = ShielddHexCodec.encode bytes := by
  simpa only [encodedString, List.nil_append] using
    (extend_ascii [] _ (ShielddHexSourceSequence.encode_ascii bytes))

theorem hex_string_decode (bytes : List GroupByteCodec.Byte) :
    ShielddHexSourceSequence.decode (encodedString bytes) = .ok bytes := by
  rw [hex_string_bytes]
  exact ShielddHexSourceSequence.roundtrip_result bytes

theorem hex_string_length (bytes : List GroupByteCodec.Byte) :
    (encodedString bytes).length = 2 * bytes.length := by
  rw [hex_string_bytes]
  exact ShielddHexCodec.encode_length bytes

set_option pp.all true in
#check @utf8_ascii
#print axioms utf8_ascii
set_option pp.all true in
#check @push_ascii
#print axioms push_ascii
set_option pp.all true in
#check @extend_append
#print axioms extend_append
set_option pp.all true in
#check @extend_ascii
#print axioms extend_ascii
set_option pp.all true in
#check @hex_string_bytes
#print axioms hex_string_bytes
set_option pp.all true in
#check @hex_string_decode
#print axioms hex_string_decode
set_option pp.all true in
#check @hex_string_length
#print axioms hex_string_length

end ShielddSecurity.ShielddHexStringOperations
