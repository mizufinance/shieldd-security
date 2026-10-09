import ShielddSecurity.GroupScalarCodec
import ShielddSecurity.RoutingLowWord
import ShielddSecurity.ShielddNativeScalar

set_option maxHeartbeats 400000

namespace ShielddSecurity.AddressBytePacking

abbrev Byte := Fin 256

/-- Each unsigned byte contributes eight bits, least significant first. -/
def byteBits (bytes : List Byte) : List Bool :=
  bytes.flatMap (fun byte => GroupScalarCodec.readBits 8 byte.val)

def littleValue : List Byte → Nat
  | [] => 0
  | byte :: tail => byte.val + 256 * littleValue tail

theorem byte_bits_length (bytes : List Byte) :
    (byteBits bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte tail ih =>
    change (GroupScalarCodec.readBits 8 byte.val ++ byteBits tail).length =
      8 * (tail.length + 1)
    rw [List.length_append, GroupScalarCodec.reader_length, ih]
    omega

theorem byte_bits_append (first second : List Byte) :
    byteBits (first ++ second) = byteBits first ++ byteBits second := by
  simp only [byteBits, List.flatMap_append]

/-- The byte/binary recurrence is symbolic in the number of bytes. -/
theorem byte_bits_value (bytes : List Byte) :
    binary (byteBits bytes) = littleValue bytes := by
  induction bytes with
  | nil => rfl
  | cons byte tail ih =>
    change binary (GroupScalarCodec.readBits 8 byte.val ++ byteBits tail) = _
    rw [RoutingLowWord.binary_append,
      GroupScalarCodec.reader_value 8 byte.val byte.isLt,
      GroupScalarCodec.reader_length, ih]
    rfl

theorem byte_bits_take (bytes : List Byte) (count : Nat) (inside : count ≤ bytes.length) :
    byteBits (bytes.take count) = (byteBits bytes).take (8 * count) := by
  have width : (byteBits (bytes.take count)).length = 8 * count := by
    rw [byte_bits_length, List.length_take, Nat.min_eq_left inside]
  have split := byte_bits_append (bytes.take count) (bytes.drop count)
  rw [List.take_append_drop] at split
  rw [split, ← width, List.take_append_length]

theorem byte_bits_drop (bytes : List Byte) (count : Nat) (inside : count ≤ bytes.length) :
    byteBits (bytes.drop count) = (byteBits bytes).drop (8 * count) := by
  have width : (byteBits (bytes.take count)).length = 8 * count := by
    rw [byte_bits_length, List.length_take, Nat.min_eq_left inside]
  have split := byte_bits_append (bytes.take count) (bytes.drop count)
  rw [List.take_append_drop] at split
  rw [split, ← width, List.drop_append_length]

theorem word_bound (bytes : List Byte) (width : bytes.length ≤ 31) :
    littleValue bytes < Scalar.modulus := by
  have bound := binary_bound (byteBits bytes)
  rw [byte_bits_value, byte_bits_length] at bound
  have powers : 2 ^ (8 * bytes.length) ≤ 2 ^ 248 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have small : littleValue bytes < 2 ^ 248 := lt_of_lt_of_le bound powers
  exact lt_trans small (by decide : 2 ^ 248 < Scalar.modulus)

variable {F : Type} [Field F] {Raw : Type}

/-- The pinned pack_bytes inner body: reverse the byte chunk, then fold the
actual Scalar wrappers with acc*256+byte. Only global primitive laws are used. -/
def nativeFold (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : List Byte) (initial : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativeScalar.Wrapped Raw :=
  bytes.reverse.foldl (fun acc byte =>
    ShielddNativeScalar.add operations
      (ShielddNativeScalar.mul operations acc (ShielddNativeScalar.fromU64 operations 256))
      (ShielddNativeScalar.fromU64 operations byte.val)) initial

theorem native_fold_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : List Byte) (initial : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativeScalar.value operations (nativeFold operations bytes initial) =
      (littleValue bytes : F) + (256 : F) ^ bytes.length *
        ShielddNativeScalar.value operations initial := by
  induction bytes with
  | nil => simp [nativeFold, littleValue]
  | cons byte tail ih =>
    have byteBound : byte.val < 2^64 := lt_trans byte.isLt (by decide)
    simp only [nativeFold, List.reverse_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [ShielddNativeScalar.add_value, ShielddNativeScalar.mul_value,
      ShielddNativeScalar.from_u64_value operations 256 (by decide),
      ShielddNativeScalar.from_u64_value operations byte.val byteBound]
    change (ShielddNativeScalar.value operations (nativeFold operations tail initial)) *
      (256 : F) + (byte.val : F) = _
    rw [ih]
    simp only [littleValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      List.length_cons, pow_succ]
    ring

def nativeWord (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : List Byte) : ShielddNativeScalar.Wrapped Raw :=
  nativeFold operations bytes (ShielddNativeScalar.zero operations)

theorem native_word_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : List Byte) :
    ShielddNativeScalar.value operations (nativeWord operations bytes) =
      (binary (byteBits bytes) : F) := by
  rw [nativeWord, native_fold_value, ShielddNativeScalar.zero_value,
    mul_zero, add_zero, byte_bits_value]

/-- Every in-range byte slice agrees with the circuit's corresponding bit
slice. In particular the 31/31/2 address chunks have widths248/248/16. -/
theorem slice_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : List Byte) (start count : Nat) (inside : start + count ≤ bytes.length) :
    ShielddNativeScalar.value operations
      (nativeWord operations ((bytes.drop start).take count)) =
      (binary (((byteBits bytes).drop (8 * start)).take (8 * count)) : F) := by
  rw [native_word_value, byte_bits_take _ count (by simp only [List.length_drop]; omega),
    byte_bits_drop bytes start (by omega)]

/-- This last substitution requires the separately proved actual assertion
and bit operands. It has no desired native ciphertext result as a premise. -/
theorem cipher_from_slice (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : List Byte) (start count : Nat) (inside : start + count ≤ bytes.length)
    (cipher stream : F)
    (assertion : cipher = stream +
      (binary (((byteBits bytes).drop (8 * start)).take (8 * count)) : F)) :
    cipher = stream + ShielddNativeScalar.value operations
      (nativeWord operations ((bytes.drop start).take count)) := by
  rw [slice_value operations bytes start count inside]
  exact assertion

set_option pp.all true in
#check @byte_bits_length
#print axioms byte_bits_length
set_option pp.all true in
#check @byte_bits_append
#print axioms byte_bits_append
set_option pp.all true in
#check @byte_bits_value
#print axioms byte_bits_value
set_option pp.all true in
#check @byte_bits_take
#print axioms byte_bits_take
set_option pp.all true in
#check @byte_bits_drop
#print axioms byte_bits_drop
set_option pp.all true in
#check @word_bound
#print axioms word_bound
set_option pp.all true in
#check @native_fold_value
#print axioms native_fold_value
set_option pp.all true in
#check @native_word_value
#print axioms native_word_value
set_option pp.all true in
#check @slice_value
#print axioms slice_value
set_option pp.all true in
#check @cipher_from_slice
#print axioms cipher_from_slice

end ShielddSecurity.AddressBytePacking
