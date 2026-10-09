import ShielddSecurity.GroupByteCodec

set_option maxHeartbeats 400000

namespace ShielddSecurity.PointAddressBytes

theorem top_byte_value (low parity : Nat) (small : low < 128) :
    low ||| (parity <<< 7) = low + 128 * parity := by
  rw [Nat.shiftLeft_eq]
  have combined := Nat.two_pow_add_eq_or_of_lt (i := 7) small parity
  norm_num only [Nat.reducePow] at combined
  rw [Nat.mul_comm parity 128, Nat.or_comm]
  exact combined.symm.trans (by omega)

theorem top_byte_low_bit (low parity offset : Nat) (small : low < 128)
    (inside : offset < 7) :
    (low ||| (parity <<< 7)) / 2^offset % 2 = low / 2^offset % 2 := by
  rw [top_byte_value low parity small]
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
      offset = 4 ∨ offset = 5 ∨ offset = 6 := by omega
  rcases cases with h | h | h | h | h | h | h <;>
    subst offset <;> norm_num <;> omega

theorem top_byte_high_bit (low parity : Nat) (small : low < 128)
    (bit : parity < 2) :
    (low ||| (parity <<< 7)) / 128 % 2 = parity := by
  rw [top_byte_value low parity small]
  omega

variable {F : Type} [Field F]
variable (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)

/-- The owned point_bytes body reverses Scalar::encode(y), then ORs the low
bit of encode(x)[31] into the last byte. The source's OR is retained exactly. -/
def pointByte (x y : F) (index : Fin 32) : Fin 256 :=
  if index.val = 31 then
    ⟨(GroupByteCodec.reverseBytes (writer.encode y) index).val |||
      (((writer.encode x ⟨31, by decide⟩).val &&& 1) <<< 7), by
      apply Nat.or_lt_two_pow (n := 8)
      · exact (GroupByteCodec.reverseBytes (writer.encode y) index).isLt
      · rw [Nat.and_one_is_mod, Nat.shiftLeft_eq]
        have bounded := Nat.mod_lt (writer.encode x ⟨31, by decide⟩).val (by decide : 0 < 2)
        norm_num only [Nat.reducePow]
        omega⟩
  else GroupByteCodec.reverseBytes (writer.encode y) index

def pointBit (x y : F) (index : Nat) : Bool :=
  if inside : index < 256 then
    decide ((pointByte codec writer x y ⟨index / 8, by omega⟩).val /
      2^(index % 8) % 2 = 1)
  else false

def pointBits (x y : F) : List Bool :=
  (List.range 256).map (pointBit codec writer x y)

private theorem parity_value (x : F) :
    (writer.encode x ⟨31, by decide⟩).val &&& 1 = codec.decode x % 2 := by
  rw [writer.byteValue, Nat.and_one_is_mod]
  have low := GroupScalarCodec.low_byte_bit (codec.decode x) 0 (by decide)
  simpa only [GroupScalarCodec.bigEndianByte, Nat.sub_self, Nat.mul_zero,
    Nat.pow_zero, Nat.div_one] using low

private theorem reversed_value (y : F) (index : Fin 32) :
    (GroupByteCodec.reverseBytes (writer.encode y) index).val =
      codec.decode y / 2^(8 * index.val) % 256 := by
  simp only [GroupByteCodec.reverseBytes, writer.byteValue, GroupScalarCodec.bigEndianByte]
  have twice : 31 - (31 - index.val) = index.val := by have := index.isLt; omega
  rw [twice]

private theorem last_small (y : F) : codec.decode y / 2^248 % 256 < 128 := by
  have width := lt_trans (codec.bounded y) GroupScalarCodec.circuit_field_width
  have quotient : codec.decode y / 2^248 < 128 := by
    norm_num only [Nat.reducePow] at width ⊢
    omega
  exact lt_of_le_of_lt (Nat.mod_le _ _) quotient

/-- Every index agrees with canonical y's low255 bits; the final bit is the
canonical x parity. No point-output or encoded-address result is assumed. -/
theorem point_bit_value (x y : F) (index : Nat) (inside : index < 256) :
    pointBit codec writer x y index =
      if index < 255 then decide (codec.decode y / 2^index % 2 = 1)
      else decide (codec.decode x % 2 = 1) := by
  unfold pointBit
  rw [dif_pos inside]
  by_cases lower : index < 255
  · rw [if_pos lower]
    have same :
        (pointByte codec writer x y ⟨index / 8, by omega⟩).val / 2^(index % 8) % 2 =
        GroupScalarCodec.bigEndianByte (codec.decode y) (31 - index / 8) /
          2^(index % 8) % 2 := by
      by_cases last : index / 8 = 31
      · simp only [pointByte, last, ite_true, Fin.val_mk]
        rw [parity_value codec writer, reversed_value codec writer]
        have offset : index % 8 < 7 := by omega
        change (codec.decode y / 2^248 % 256 ||| ((codec.decode x % 2) <<< 7)) /
          2^(index % 8) % 2 = (codec.decode y / 2^248 % 256) / 2^(index % 8) % 2
        exact top_byte_low_bit _ _ _ (last_small codec y) offset
      · simp only [pointByte, last, ite_false]
        rw [reversed_value codec writer]
        unfold GroupScalarCodec.bigEndianByte
        have twice : 31 - (31 - index / 8) = index / 8 := by omega
        rw [twice]
    rw [same]
    exact GroupScalarCodec.encoded_bit_formula (codec.decode y) index lower
  · have final : index = 255 := by omega
    subst index
    rw [if_neg (by decide : ¬255 < 255)]
    simp only [pointByte, Nat.reduceDiv, Nat.reduceMod, ite_true, Fin.val_mk]
    rw [parity_value codec writer, reversed_value codec writer]
    change decide (((codec.decode y / 2^248 % 256 ||| ((codec.decode x % 2) <<< 7)) /
      128 % 2) = 1) = decide (codec.decode x % 2 = 1)
    rw [top_byte_high_bit _ _ (last_small codec y) (Nat.mod_lt _ (by decide))]

theorem point_reader_join (x y : F) :
    pointBits codec writer x y = GroupScalarCodec.readBits 255 (codec.decode y) ++
      [decide (codec.decode x % 2 = 1)] := by
  apply List.ext_getElem
  · simp only [pointBits, List.length_map, List.length_range, List.length_append,
      GroupScalarCodec.reader_length, List.length_singleton]
  · intro index leftBound rightBound
    have inside : index < 256 := by simpa only [pointBits, List.length_map, List.length_range] using leftBound
    simp only [pointBits, List.getElem_map, List.getElem_range]
    rw [point_bit_value codec writer x y index inside]
    by_cases lower : index < 255
    · rw [if_pos lower, List.getElem_append_left (by rw [GroupScalarCodec.reader_length]; exact lower)]
      exact (GroupScalarCodec.reader_index 255 (codec.decode y) index lower).symm
    · have final : index = 255 := by omega
      subst index
      simp only [Nat.lt_irrefl, ite_false]
      rw [List.getElem_append_right (by rw [GroupScalarCodec.reader_length])]
      simp only [GroupScalarCodec.reader_length, Nat.sub_self, List.getElem_cons_zero]

set_option pp.all true in
#check @top_byte_value
#print axioms top_byte_value
set_option pp.all true in
#check @top_byte_low_bit
#print axioms top_byte_low_bit
set_option pp.all true in
#check @top_byte_high_bit
#print axioms top_byte_high_bit
set_option pp.all true in
#check @point_bit_value
#print axioms point_bit_value
set_option pp.all true in
#check @point_reader_join
#print axioms point_reader_join

end ShielddSecurity.PointAddressBytes
