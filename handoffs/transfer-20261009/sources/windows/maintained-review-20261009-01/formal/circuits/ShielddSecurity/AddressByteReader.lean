import ShielddSecurity.AddressBytePacking
import ShielddSecurity.PointAddressBytes

set_option maxHeartbeats 400000

namespace ShielddSecurity.AddressByteReader

open AddressBytePacking

/-- The flat eight-bit byte expansion uses exactly byte[index/8] and the
source's index%8 bit offset. The proof recurs on bytes, never on a wide row walk. -/
theorem byte_bits_index (bytes : List Byte) (index : Nat) (inside : index < 8 * bytes.length) :
    (byteBits bytes)[index]'(by rw [byte_bits_length]; exact inside) =
      decide ((bytes[index / 8]'(by omega)).val / 2^(index % 8) % 2 = 1) := by
  induction bytes generalizing index with
  | nil => simp at inside
  | cons byte tail ih =>
    change (GroupScalarCodec.readBits 8 byte.val ++ byteBits tail)[index]'_ = _
    by_cases first : index < 8
    · rw [List.getElem_append_left (by rw [GroupScalarCodec.reader_length]; exact first),
        GroupScalarCodec.reader_index 8 byte.val index first]
      have block : index / 8 = 0 := by omega
      have offset : index % 8 = index := Nat.mod_eq_of_lt first
      simp only [block, List.getElem_cons_zero, offset]
    · rw [List.getElem_append_right (by rw [GroupScalarCodec.reader_length]; omega)]
      simp only [GroupScalarCodec.reader_length]
      rw [ih (index - 8) (by simp only [List.length_cons] at inside; omega)]
      have block : index / 8 = (index - 8) / 8 + 1 := by omega
      have offset : (index - 8) % 8 = index % 8 := by omega
      simp only [block, List.getElem_cons_succ, offset]

variable {F : Type} [Field F]
variable (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)

def pointBytes (x y : F) : List Byte := List.ofFn (PointAddressBytes.pointByte codec writer x y)

theorem point_byte_bits (x y : F) :
    byteBits (pointBytes codec writer x y) = PointAddressBytes.pointBits codec writer x y := by
  apply List.ext_getElem
  · simp only [byte_bits_length, pointBytes, List.length_ofFn,
      PointAddressBytes.pointBits, List.length_map, List.length_range]
  · intro index leftBound rightBound
    have inside : index < 256 := by
      simpa only [PointAddressBytes.pointBits, List.length_map, List.length_range] using rightBound
    rw [byte_bits_index _ index (by simp only [pointBytes, List.length_ofFn]; omega)]
    simp only [pointBytes, List.getElem_ofFn, PointAddressBytes.pointBits,
      List.getElem_map, List.getElem_range, PointAddressBytes.pointBit, dif_pos inside]

theorem point_bytes_reader (x y : F) :
    byteBits (pointBytes codec writer x y) = GroupScalarCodec.readBits 255 (codec.decode y) ++
      [decide (codec.decode x % 2 = 1)] := by
  rw [point_byte_bits, PointAddressBytes.point_reader_join]

def addressBytes (generatorX generatorY transmissionX transmissionY : F) : List Byte :=
  pointBytes codec writer generatorX generatorY ++ pointBytes codec writer transmissionX transmissionY

theorem address_byte_bits (generatorX generatorY transmissionX transmissionY : F) :
    byteBits (addressBytes codec writer generatorX generatorY transmissionX transmissionY) =
      (GroupScalarCodec.readBits 255 (codec.decode generatorY) ++
        [decide (codec.decode generatorX % 2 = 1)]) ++
      (GroupScalarCodec.readBits 255 (codec.decode transmissionY) ++
        [decide (codec.decode transmissionX % 2 = 1)]) := by
  rw [addressBytes, byte_bits_append, point_bytes_reader, point_bytes_reader]

theorem address_length (generatorX generatorY transmissionX transmissionY : F) :
    (addressBytes codec writer generatorX generatorY transmissionX transmissionY).length = 64 := by
  simp only [addressBytes, List.length_append, pointBytes, List.length_ofFn]

set_option pp.all true in
#check @byte_bits_index
#print axioms byte_bits_index
set_option pp.all true in
#check @point_byte_bits
#print axioms point_byte_bits
set_option pp.all true in
#check @point_bytes_reader
#print axioms point_bytes_reader
set_option pp.all true in
#check @address_byte_bits
#print axioms address_byte_bits
set_option pp.all true in
#check @address_length
#print axioms address_length

end ShielddSecurity.AddressByteReader
