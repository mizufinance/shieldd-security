import ShielddSecurity.ShielddNativeEncode

set_option maxHeartbeats 100000

namespace ShielddSecurity.ShielddNativeByteBit

/-- Unsigned byte shift/mask has the mathematical quotient/modulo meaning
already used by GroupByteCodec's exact indexed reader. This lemma connects
that numeric0/1 to its Boolean view, before Scalar::from(u64) is called. -/
def masked (bytes : GroupByteCodec.Bytes) (index : Nat) : Nat :=
  GroupByteCodec.byteAt bytes (31-index/8) / 2^(index%8) % 2

theorem reader_bit_value (bytes : GroupByteCodec.Bytes) (index : Nat) :
    (GroupByteCodec.readerBit bytes index).toNat = masked bytes index := by
  have small : masked bytes index < 2 := Nat.mod_lt _ (by decide)
  by_cases one : masked bytes index = 1
  · change (decide (masked bytes index = 1)).toNat = masked bytes index
    rw [one]
    rfl
  · have zero : masked bytes index = 0 := by omega
    change (decide (masked bytes index = 1)).toNat = masked bytes index
    rw [zero]
    rfl

/-- Exact raw constructor agreement, stronger than field-value agreement:
the source's unsigned masked integer and the derived Bool use the SAME
fromU64 primitive argument. No Boolean premise for a field input is needed. -/
theorem masked_scalar_eq_bit {F Raw : Type} [Field F]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : GroupByteCodec.Bytes) (index : Nat) :
    ShielddNativeScalar.fromU64 operations (masked bytes index) =
      ShielddNativeMultiply.bitScalar operations (GroupByteCodec.readerBit bytes index) := by
  unfold ShielddNativeMultiply.bitScalar
  rw [reader_bit_value]

/-- The whole source byte-bit map, with its actual255 indexed positions,
is therefore the list consumed by the previously proved raw native loop. -/
theorem indexed_scalar_bits {F Raw : Type} [Field F]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bytes : GroupByteCodec.Bytes) :
    (List.range 255).map (fun index => ShielddNativeScalar.fromU64 operations (masked bytes index)) =
      (GroupByteCodec.reader bytes).map (ShielddNativeMultiply.bitScalar operations) := by
  unfold GroupByteCodec.reader
  rw [List.map_map]
  apply List.map_congr_left
  intro index member
  exact masked_scalar_eq_bit operations bytes index

set_option pp.all true in
#check @reader_bit_value
#print axioms reader_bit_value
set_option pp.all true in
#check @masked_scalar_eq_bit
#print axioms masked_scalar_eq_bit
set_option pp.all true in
#check @indexed_scalar_bits
#print axioms indexed_scalar_bits

end ShielddSecurity.ShielddNativeByteBit
