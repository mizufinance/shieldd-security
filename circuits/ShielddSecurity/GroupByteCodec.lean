import ShielddSecurity.GroupScalarCodec
import ShielddSecurity.TransferReduction

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupByteCodec

abbrev Byte := Fin 256
abbrev Bytes := Fin 32 → Byte

/-- Total indexing has the Rust array value at every in-range index. The
native255-bit reader never takes the out-of-range branch. -/
def byteAt (bytes : Bytes) (index : Nat) : Nat :=
  if valid : index < 32 then (bytes ⟨index,valid⟩).val else 0

theorem byte_at_valid (bytes : Bytes) (index : Nat) (valid : index < 32) :
    byteAt bytes index = (bytes ⟨index,valid⟩).val := by
  simp only [byteAt,dif_pos valid]

/-- Exact pinned group.rs161-167 indexing of an actual32-byte buffer, with
unsigned byte right-shift and low-bit mask interpreted as division/modulo.
The bit is converted to field zero/one by GroupNativeMultiply's Boolean view. -/
def readerBit (bytes : Bytes) (index : Nat) : Bool :=
  decide (byteAt bytes (31-index/8) / 2^(index%8) % 2 = 1)

def reader (bytes : Bytes) : List Bool := (List.range 255).map (readerBit bytes)

variable {F : Type} [Field F]

/-- Global pinned primitive boundary, for every field value and every byte.
Scalar::as_slice uses blst_scalar_from_fr and blst_bendian_from_scalar;
Write copies those32 bytes. This contract identifies that native encoder with
the SAME canonical prime-field decoder used by the circuit's scalar proofs.
It neither mentions a group output nor asserts any witness's scalar bound. -/
structure BEWrite (codec : TransferReduction.CanonicalField F) where
  encode : F → Bytes
  byteValue : ∀ value index,
    (encode value index).val = GroupScalarCodec.bigEndianByte (codec.decode value) index.val

/-- The byte contract has a mathematical inhabitant for every codec; its
instantiation for the pinned native FFI encoder is a separate source contract. -/
def canonicalWrite (codec : TransferReduction.CanonicalField F) : BEWrite codec where
  encode value index := ⟨GroupScalarCodec.bigEndianByte (codec.decode value) index.val,
    Nat.mod_lt _ (by decide)⟩
  byteValue _ _ := rfl

theorem reader_join (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (value : F) : reader (writer.encode value) = GroupScalarCodec.encodedBits (codec.decode value) := by
  unfold reader GroupScalarCodec.encodedBits
  apply List.map_congr_left
  intro index member
  have safe := GroupScalarCodec.native_reader_indices index (List.mem_range.mp member)
  unfold readerBit GroupScalarCodec.encodedBit
  rw [byte_at_valid _ _ safe.2.1,writer.byteValue]

/-- Native buffer multiplication follows from the explicit byte contract and
the independently supplied standard full-Jubjub group model. In its intended
instance J is the full curve group; native SubgroupPoint values embed into J.
SubgroupPoint alone cannot meet StandardCurveModel.covers, which includes
torsion. This lemma assumes neither a desired scalar result nor subgroupness. -/
theorem native_reader_coordinates [CharP F Scalar.modulus] {J : Type} [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (two : (2 : F) ≠ 0) (base : J) (value : F) :
    GroupNativeMultiply.nativeMultiply d (model.coordinates base) (reader (writer.encode value)) =
      model.coordinates (codec.decode value • base) := by
  rw [reader_join,GroupScalarCodec.encoded_reader]
  exact GroupScalarCodec.native_field_coordinates d imaginary model nonSquare
    imaginarySquare two base (codec.decode value) (codec.bounded value)

theorem canonical_reader_join [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (bits : List Bool) (width : bits.length = 252) (value : F)
    (bound : binary bits < Scalar.order) (reconstruction : (binary bits : F) = value) :
    reader (writer.encode value) = bits ++ [false,false,false] := by
  have decoded : codec.decode value = binary bits := by
    rw [← reconstruction]
    exact TransferReduction.decode_canonical_cast codec _
      (lt_trans bound (by decide : Scalar.order < Scalar.modulus))
  rw [reader_join,GroupScalarCodec.encoded_reader,decoded]
  exact GroupScalarCodec.canonical_reader_join bits width (binary bits) bound rfl

/-- The native coordinate path reverses SDK affine u/v's32-byte little-endian
encoding before Scalar::read_cfg AllowZero. This independent read contract
requires only canonical coordinate bytes; it asserts no curve or subgroup fact. -/
structure BERead where
  decode : Bytes → Option F
  canonical : ∀ value : Nat, value < Scalar.modulus → ∀ bytes : Bytes,
    (∀ index, (bytes index).val = GroupScalarCodec.bigEndianByte value index.val) →
    decode bytes = some (value : F)

def reverseBytes (bytes : Bytes) : Bytes := fun index =>
  bytes ⟨31-index.val,by have := index.isLt; omega⟩

def littleEndianByte (value index : Nat) : Nat := value / 2^(8*index) % 256

theorem reversed_coordinate_read (decoder : BERead (F := F)) (value : Nat)
    (bound : value < Scalar.modulus) (bytes : Bytes)
    (coordinateBytes : ∀ index, (bytes index).val = littleEndianByte value index.val) :
    decoder.decode (reverseBytes bytes) = some (value : F) := by
  apply decoder.canonical value bound
  intro index
  dsimp only [reverseBytes]
  rw [coordinateBytes]
  rfl

set_option pp.all true in
#check @byte_at_valid
#print axioms byte_at_valid
set_option pp.all true in
#check @canonicalWrite
#print axioms canonicalWrite
set_option pp.all true in
#check @reader_join
#print axioms reader_join
set_option pp.all true in
#check @native_reader_coordinates
#print axioms native_reader_coordinates
set_option pp.all true in
#check @canonical_reader_join
#print axioms canonical_reader_join
set_option pp.all true in
#check @reversed_coordinate_read
#print axioms reversed_coordinate_read

end ShielddSecurity.GroupByteCodec
