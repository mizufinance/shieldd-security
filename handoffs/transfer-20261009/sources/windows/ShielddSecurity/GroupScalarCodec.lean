import ShielddSecurity.GroupNativeMultiply
import ShielddSecurity.Scalar

set_option maxHeartbeats 300000

/-! Scalar-width bridge for the owned `group.rs::Point<Scalar>::multiply`
reader at shieldd.lock844389ee069e1fb2e576708842d0b389b4d9a44a.
The source reads255 ascending bits from canonical big-endian Scalar::encode,
using bytes[31-i/8] >> (i%8) & 1. The recursive mathematical reader below
consumes the same canonical integer least-significant bit first. Upstream
canonical encoding and the source/byte-reader interpretation remain explicit
contracts; this module proves the width and multiplication consequences rather
than asserting byte/source refinement. Circuit canonical scalars use252 bits.
No particular assignment's scalar, output or subgroup membership is assumed. -/
namespace ShielddSecurity.GroupScalarCodec

def readBits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value => decide (value % 2 = 1) :: readBits width (value / 2)

theorem reader_length (width value : Nat) : (readBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [readBits, List.length_cons, ih]

/-- Exact owned native byte index and bit offset, including the odd255th bit. -/
theorem native_reader_indices (index : Nat) (bound : index < 255) :
    index / 8 ≤ 31 ∧ 31 - index / 8 < 32 ∧ index % 8 < 8 ∧
      31 - (31 - index / 8) = index / 8 := by
  omega

def bigEndianByte (value index : Nat) : Nat :=
  value / 2 ^ (8 * (31 - index)) % 256

def encodedBit (value index : Nat) : Bool :=
  decide (bigEndianByte value (31 - index / 8) / 2 ^ (index % 8) % 2 = 1)

/-- Eight fixed byte offsets; no scalar-width walk is unrolled. -/
theorem low_byte_bit (value offset : Nat) (bound : offset < 8) :
    value % 256 / 2 ^ offset % 2 = value / 2 ^ offset % 2 := by
  have offsetCases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
      offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases offsetCases with h | h | h | h | h | h | h | h <;>
    subst offset <;> norm_num <;> omega

theorem encoded_bit_formula (value index : Nat) (bound : index < 255) :
    encodedBit value index = decide (value / 2 ^ index % 2 = 1) := by
  have safe := native_reader_indices index bound
  unfold encodedBit bigEndianByte
  rw [safe.2.2.2, low_byte_bit _ _ safe.2.2.1, Nat.div_div_eq_div_mul]
  have powers : 2 ^ (8 * (index / 8)) * 2 ^ (index % 8) = 2 ^ index := by
    rw [← pow_add]
    congr 1
    have division := Nat.mod_add_div index 8
    omega
  rw [powers]

theorem reader_index (width value index : Nat) (bound : index < width) :
    (readBits width value)[index]'(by rw [reader_length]; exact bound) =
      decide (value / 2 ^ index % 2 = 1) := by
  induction width generalizing value index with
  | zero => omega
  | succ width ih =>
      cases index with
      | zero => simp [readBits]
      | succ index =>
          simp only [readBits, List.getElem_cons_succ]
          rw [ih (value / 2) index (by omega)]
          simp [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

def encodedBits (value : Nat) : List Bool :=
  (List.range 255).map (encodedBit value)

/-- The source's indexed32-byte reader equals the recursive integer reader.
Its input-byte interpretation is the upstream canonical big-endian encoding
contract, rather than an assumption about any multiplication output. -/
theorem encoded_reader (value : Nat) : encodedBits value = readBits 255 value := by
  apply List.ext_getElem
  · simp [encodedBits, reader_length]
  · intro index leftBound rightBound
    have bound : index < 255 := by simpa [reader_length] using rightBound
    simp only [encodedBits, List.getElem_map, List.getElem_range]
    rw [encoded_bit_formula value index bound, reader_index 255 value index bound]

theorem reader_value (width value : Nat) (bound : value < 2 ^ width) :
    binary (readBits width value) = value := by
  induction width generalizing value with
  | zero =>
      have zero : value = 0 := by simpa using bound
      simp [readBits, binary, zero]
  | succ width ih =>
      have remainder := Nat.mod_lt value (by decide : 0 < 2)
      have decomposition := Nat.mod_add_div value 2
      have smaller : value / 2 < 2 ^ width := by
        simp only [pow_succ] at bound
        omega
      have bit : (if decide (value % 2 = 1) then 1 else 0 : Nat) = value % 2 := by
        by_cases one : value % 2 = 1
        · simp [one]
        · have zero : value % 2 = 0 := by omega
          simp [zero]
      simp only [readBits, binary, ih _ smaller, bit]
      omega

theorem false_tail_value (bits : List Bool) (count : Nat) :
    binary (bits ++ List.replicate count false) = binary bits := by
  have zeros : ∀ n : Nat, binary (List.replicate n false) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, binary, ih]
  induction bits with
  | nil => exact zeros count
  | cons bit tail ih => simp only [List.cons_append, binary, ih]

theorem binary_injective_same_width (left right : List Bool)
    (width : left.length = right.length) (value : binary left = binary right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons bit tail => simp at width
  | cons bit tail ih =>
      cases right with
      | nil => simp at width
      | cons other rest =>
          have lengths : tail.length = rest.length := Nat.succ.inj width
          have sameBit : bit = other := by
            cases bit <;> cases other <;> simp [binary] at value ⊢ <;> omega
          subst other
          have sameTail : binary tail = binary rest := by
            simp only [binary] at value
            omega
          rw [ih rest lengths sameTail]

theorem scalar_order_width : Scalar.order < 2 ^ 252 := by
  norm_num [Scalar.order]
  omega

theorem circuit_field_width : Scalar.modulus < 2 ^ 255 := by
  norm_num [Scalar.modulus]
  omega

/-- Canonical circuit reconstruction uniquely determines the actual255-bit
integer reader: the extra three most significant bits are zero. -/
theorem canonical_reader_join (bits : List Bool) (width : bits.length = 252)
    (value : Nat) (canonical : value < Scalar.order) (reconstruction : binary bits = value) :
    readBits 255 value = bits ++ [false, false, false] := by
  apply binary_injective_same_width
  · simp [reader_length, width]
  · rw [reader_value 255 value (by have := scalar_order_width; omega)]
    simpa only [show [false, false, false] = List.replicate 3 false from rfl,
      false_tail_value] using reconstruction.symm

variable {F : Type} [Field F]

/-- Every canonical circuit-field value fits the full native reader; this
also covers cofactor-preimage scalars rather than just canonical Fr inputs. -/
theorem native_field_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (base : J) (value : Nat) (canonical : value < Scalar.modulus) :
    GroupNativeMultiply.nativeMultiply d (model.coordinates base) (readBits 255 value) =
      model.coordinates (value • base) := by
  rw [GroupNativeMultiply.native_multiply_coordinates d imaginary model nonSquare
    imaginarySquare two, reader_value 255 value (lt_trans canonical circuit_field_width)]

/-- The extra encoded width does not change the owned native loop's output.
The field/codec source view and standard curve facts are separate contracts. -/
theorem native_canonical_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (base : J) (bits : List Bool) (width : bits.length = 252)
    (value : Nat) (canonical : value < Scalar.order) (reconstruction : binary bits = value) :
    GroupNativeMultiply.nativeMultiply d (model.coordinates base) (readBits 255 value) =
      GroupNativeMultiply.nativeMultiply d (model.coordinates base) bits := by
  rw [GroupNativeMultiply.native_multiply_coordinates d imaginary model nonSquare
    imaginarySquare two, GroupNativeMultiply.native_multiply_coordinates d imaginary
    model nonSquare imaginarySquare two,
    reader_value 255 value (by have := scalar_order_width; omega), reconstruction]

set_option pp.all true in
#check @reader_length
#print axioms reader_length
set_option pp.all true in
#check @native_reader_indices
#print axioms native_reader_indices
set_option pp.all true in
#check @low_byte_bit
#print axioms low_byte_bit
set_option pp.all true in
#check @encoded_bit_formula
#print axioms encoded_bit_formula
set_option pp.all true in
#check @reader_index
#print axioms reader_index
set_option pp.all true in
#check @encoded_reader
#print axioms encoded_reader
set_option pp.all true in
#check @reader_value
#print axioms reader_value
set_option pp.all true in
#check @false_tail_value
#print axioms false_tail_value
set_option pp.all true in
#check @binary_injective_same_width
#print axioms binary_injective_same_width
set_option pp.all true in
#check @scalar_order_width
#print axioms scalar_order_width
set_option pp.all true in
#check @circuit_field_width
#print axioms circuit_field_width
set_option pp.all true in
#check @canonical_reader_join
#print axioms canonical_reader_join
set_option pp.all true in
#check @native_field_coordinates
#print axioms native_field_coordinates
set_option pp.all true in
#check @native_canonical_coordinates
#print axioms native_canonical_coordinates

end ShielddSecurity.GroupScalarCodec
