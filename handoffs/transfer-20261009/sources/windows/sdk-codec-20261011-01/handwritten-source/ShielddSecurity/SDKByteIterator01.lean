import ShielddSecurity.GroupScalarCodec

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKByteIterator01

/-- Mathematical byte and bit iterators corresponding to jubjub0.10.0's
reversed-byte, reversed-inner-bit, skip(4) multiplication loop. Actual Rust
byte/iterator representation is a separate refinement boundary. -/
def byteBits (byte : Nat) : List Bool :=
  (List.range 8).map (fun offset => decide (byte / 2 ^ offset % 2 = 1))

def ascending (bytes : List Nat) : List Bool := bytes.flatMap byteBits

def descending (bytes : List Nat) : List Bool :=
  bytes.reverse.flatMap (fun byte =>
    (List.range 8).reverse.map (fun offset => decide (byte / 2 ^ offset % 2 = 1)))

def retained (bytes : List Nat) : List Bool := (descending bytes).drop 4

def canonicalBytes (count value : Nat) : List Nat :=
  (List.range count).map (fun index => value / 2 ^ (8 * index) % 256)

theorem range_blocks (count width : Nat) :
    (List.range count).flatMap (fun block =>
      (List.range width).map (fun offset => block * width + offset)) =
    List.range (count * width) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]
      rw [Nat.succ_mul, List.range_add]

theorem descending_reverse (bytes : List Nat) :
    descending bytes = (ascending bytes).reverse := by
  simp only [descending, ascending, List.reverse_flatMap, byteBits,
    Function.comp_def, List.map_reverse]

theorem byte_bit_formula (value block offset : Nat) (bound : offset < 8) :
    (value / 2 ^ (8 * block) % 256) / 2 ^ offset % 2 =
      value / 2 ^ (block * 8 + offset) % 2 := by
  rw [GroupScalarCodec.low_byte_bit _ _ bound, Nat.div_div_eq_div_mul,
    ← pow_add, Nat.mul_comm 8 block]

theorem ascending_canonical (count value : Nat) :
    ascending (canonicalBytes count value) =
      (List.range (count * 8)).map (fun index => decide (value / 2 ^ index % 2 = 1)) := by
  rw [← range_blocks count 8, List.map_flatMap]
  simp only [ascending, canonicalBytes, List.flatMap_map, Function.comp_def,
    byteBits, List.map_map]
  apply congrArg (List.flatMap · (List.range count))
  funext block
  apply List.map_congr_left
  intro offset member
  rw [byte_bit_formula value block offset (List.mem_range.mp member)]

theorem range_reader (width value : Nat) :
    (List.range width).map (fun index => decide (value / 2 ^ index % 2 = 1)) =
      GroupScalarCodec.readBits width value := by
  apply List.ext_getElem
  · simp [GroupScalarCodec.reader_length]
  · intro index leftBound rightBound
    have bound : index < width := by simpa [GroupScalarCodec.reader_length] using rightBound
    simp only [List.getElem_map, List.getElem_range]
    exact (GroupScalarCodec.reader_index width value index bound).symm

theorem retained_canonical (value : Nat) :
    retained (canonicalBytes 32 value) = (GroupScalarCodec.readBits 252 value).reverse := by
  rw [retained, descending_reverse, ascending_canonical, List.drop_reverse]
  simp only [List.length_map, List.length_range]
  rw [← List.map_take, List.take_range]
  norm_num only
  rw [min_eq_left (by decide : 252 ≤ 256)]
  rw [range_reader]

end ShielddSecurity.SDKByteIterator01


set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.byteBits
#print axioms ShielddSecurity.SDKByteIterator01.byteBits
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.ascending
#print axioms ShielddSecurity.SDKByteIterator01.ascending
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.descending
#print axioms ShielddSecurity.SDKByteIterator01.descending
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.retained
#print axioms ShielddSecurity.SDKByteIterator01.retained
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.canonicalBytes
#print axioms ShielddSecurity.SDKByteIterator01.canonicalBytes
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.range_blocks
#print axioms ShielddSecurity.SDKByteIterator01.range_blocks
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.descending_reverse
#print axioms ShielddSecurity.SDKByteIterator01.descending_reverse
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.byte_bit_formula
#print axioms ShielddSecurity.SDKByteIterator01.byte_bit_formula
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.ascending_canonical
#print axioms ShielddSecurity.SDKByteIterator01.ascending_canonical
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.range_reader
#print axioms ShielddSecurity.SDKByteIterator01.range_reader
set_option pp.all true in
#check @ShielddSecurity.SDKByteIterator01.retained_canonical
#print axioms ShielddSecurity.SDKByteIterator01.retained_canonical
