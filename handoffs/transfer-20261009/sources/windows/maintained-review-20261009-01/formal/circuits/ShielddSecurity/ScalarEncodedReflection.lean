import ShielddSecurity.GroupScalarCodec
import ShielddSecurity.ScalarBits

set_option maxHeartbeats 200000

namespace ShielddSecurity.ScalarEncodedReflection

variable {F : Type} [Field F]

/-- A finite Boolean word is the encoding of its own decoded integer.
This uses width and binary uniqueness, without enumerating the word's values. -/
theorem decoded_word (rho : Nat → F) (bits : List Linear) (width : Nat)
    (length : bits.length = width) :
    ScalarBits.decodeBits rho bits =
      encodeBits width (binary (ScalarBits.decodeBits rho bits)) := by
  have decodedLength : (ScalarBits.decodeBits rho bits).length = width := by
    simpa only [ScalarBits.decodeBits, List.length_map] using length
  have bound : binary (ScalarBits.decodeBits rho bits) < 2 ^ width := by
    simpa only [decodedLength] using binary_bound (ScalarBits.decodeBits rho bits)
  exact GroupScalarCodec.binary_injective_same_width _ _
    (by simp only [encodeBits_length, decodedLength])
    (encodeBits_value width _ bound).symm

/-- Reflect an actual source LC at an actual word position.
Concrete callers must establish its source position and Boolean physical row. -/
theorem source_bit_value (rho : Nat → F) (bits : List Linear) (width index : Nat)
    (lc : Linear) (length : bits.length = width) (position : bits[index]? = some lc)
    (boolean : Square (eval rho lc) (eval rho lc)) :
    eval rho lc = (if (encodeBits width (binary (ScalarBits.decodeBits rho bits)))[index]?.getD false
      then 1 else 0) := by
  have decodedPosition : (ScalarBits.decodeBits rho bits)[index]? =
      some (ScalarBits.decodeBit rho lc) := by
    simp only [ScalarBits.decodeBits, List.getElem?_map, position, Option.map_some]
  rw [← decoded_word rho bits width length, decodedPosition]
  exact ScalarBits.decoded_bit_value rho lc boolean

set_option pp.all true in
#check @decoded_word
#print axioms decoded_word
set_option pp.all true in
#check @source_bit_value
#print axioms source_bit_value

end ShielddSecurity.ScalarEncodedReflection
