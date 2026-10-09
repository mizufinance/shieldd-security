import ShielddSecurity.ElligatorChoice
import ShielddSecurity.TransferReduction

set_option maxHeartbeats 200000

namespace ShielddSecurity.ElligatorNative

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Uses the upstream canonical prime-field codec contract at every operand.
The same-parity equation must come from the actual canonical-bit and byte joins. -/
theorem codec_root_unique (codec : TransferReduction.CanonicalField F) (left right : F)
    (squares : left * left = right * right)
    (parity : codec.decode left % 2 = codec.decode right % 2) : left = right := by
  have decoded : codec.decode left = codec.decode right :=
    Elligator.canonical_root_unique (F := F) (p := Scalar.modulus) (codec.decode left) (codec.decode right)
      (codec.bounded left) (codec.bounded right) (by decide)
      (by simpa only [codec.roundtrip] using squares) parity
  calc
    left = ((codec.decode left : Nat) : F) := (codec.roundtrip left).symm
    _ = ((codec.decode right : Nat) : F) := congrArg (fun value : Nat => (value : F)) decoded
    _ = right := codec.roundtrip right

theorem first_coordinate_unique (denominator c1 actual native : F)
    (nonzero : denominator ≠ 0)
    (actualRow : denominator * actual = -c1)
    (nativeRow : denominator * native = -c1) : actual = native := by
  exact mul_left_cancel₀ nonzero (actualRow.trans nativeRow.symm)

/-- The native option's existence specification belongs to the pinned unmodified
sqrt API. The arbitrary circuit choice is proved from its QR constraint. -/
theorem choice_unique (z value root : F) (actual native : Bool)
    (nonSquare : Group.NoUnitSquare z) (zNonzero : z ≠ 0) (valueNonzero : value ≠ 0)
    (row : root * root = if actual then value else z * value)
    (nativeOption : native = true ↔ ∃ square : F, square * square = value) : actual = native := by
  have equal := (Elligator.square_choice_sound z value root actual nonSquare zNonzero
    valueNonzero row).trans nativeOption.symm
  cases actual <;> cases native <;> simp_all

variable [DecidableEq F]

/-- Joins the exact native selected root and canonical parity to the circuit's
total inverse equations. Native sqrt/codec contracts are explicit; no native map
result, arbitrary witness subgroup membership, or output equality is a premise. -/
theorem selected_point_unique (codec : TransferReduction.CanonicalField F)
    (k selectedX actualY nativeY inverse zero : F)
    (squares : actualY * actualY = nativeY * nativeY)
    (parity : codec.decode actualY % 2 = codec.decode nativeY % 2)
    (product : (((k * selectedX) + 1) * (k * actualY)) * inverse = 1 - zero)
    (annihilate : (((k * selectedX) + 1) * (k * actualY)) * zero = 0)
    (inverseZero : inverse * zero = 0) :
    (⟨inverse * ((k * selectedX) + 1) * (k * selectedX),
      inverse * (k * actualY) * ((k * selectedX) - 1) + zero⟩ : Group.Point F) =
      Elligator.rationalPoint (k * selectedX) (k * nativeY) := by
  have root := codec_root_unique codec actualY nativeY squares parity
  rw [← root]
  exact Elligator.rational_point_sound _ _ inverse zero product annihilate inverseZero

set_option pp.all true in
#check @codec_root_unique
#print axioms codec_root_unique
set_option pp.all true in
#check @first_coordinate_unique
#print axioms first_coordinate_unique
set_option pp.all true in
#check @choice_unique
#print axioms choice_unique
set_option pp.all true in
#check @selected_point_unique
#print axioms selected_point_unique

end ShielddSecurity.ElligatorNative
