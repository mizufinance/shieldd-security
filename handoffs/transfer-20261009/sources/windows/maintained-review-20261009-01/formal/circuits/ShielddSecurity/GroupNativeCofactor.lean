import ShielddSecurity.GroupNativeAuthorization

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupNativeCofactor

/-- Little-endian u64 limbs of pinned circuits/src/scalar.rs INVERSE_EIGHT.
The native Scalar::from_limbs interpretation remains a source contract;
the numerical equation and canonical bound are derived here. -/
def inverseEight : Nat :=
  6490498278660957591 + 1498858728380236304 * 2^64 +
    2363518304504940384 * 2^128 + 130523700929132021 * 2^192

theorem inverse_eight_equation : 8 * inverseEight = Scalar.order + 1 := by
  norm_num [inverseEight,Scalar.order]

theorem inverse_eight_bound : inverseEight < Scalar.modulus := by
  decide

variable {F : Type} [Field F]

/-- Pinned group.rs168-169 calls native Point::multiply on the scalar built
from INVERSE_EIGHT. The same canonical encoder is used as for randomizers. -/
def nativePreimage (d : F) (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (point : Group.Point F) : Group.Point F :=
  GroupNativeMultiply.nativeMultiply d point
    (GroupByteCodec.reader (writer.encode (inverseEight : F)))

theorem native_preimage_coordinates [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0) (point : J) :
    nativePreimage d codec writer (model.coordinates point) =
      model.coordinates (inverseEight • point) := by
  unfold nativePreimage
  rw [GroupByteCodec.native_reader_coordinates codec writer d imaginary model nonSquare
    imaginarySquare two point (inverseEight : F),
    TransferReduction.decode_canonical_cast codec inverseEight inverse_eight_bound]

/-- The subgroup input contract is independent of the constructed preimage.
In a native SDK instance it follows from the admitted SubgroupPoint input,
not from a circuit's desired output or a cofactor witness-generation closure. -/
theorem subgroup_eight_preimage {J : Type} [AddCommGroup J] (point : J)
    (subgroup : Scalar.order • point = 0) :
    (8 : Nat) • (inverseEight • point) = point := by
  rw [← mul_nsmul,Nat.mul_comm inverseEight 8,inverse_eight_equation,
    add_nsmul,subgroup,one_nsmul,zero_add]

/-- The three native addition operations supply a small constructor boundary
for the circuit's three-doubling subgroup check. Actual division/materialized
product rows still require their independently extracted coverage proofs. -/
def nativeEight (d : F) (point : Group.Point F) : Group.Point F :=
  let twice := GroupFixedWindows.nativeAdd d point point
  let four := GroupFixedWindows.nativeAdd d twice twice
  GroupFixedWindows.nativeAdd d four four

theorem native_eight_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (point : J) : nativeEight d (model.coordinates point) = model.coordinates (8 • point) := by
  have count : (((point + point) + (point + point)) +
      ((point + point) + (point + point))) = (8 : Nat) • point := by
    simp only [← two_nsmul,← mul_nsmul]
  calc
    _ = model.coordinates (((point + point) + (point + point)) +
        ((point + point) + (point + point))) := by
      simp only [nativeEight,GroupFixedWindows.native_add_coordinates d imaginary model
        nonSquare imaginarySquare]
    _ = model.coordinates (8 • point) := congrArg model.coordinates count

theorem native_preimage_complete [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (point : J) (subgroup : Scalar.order • point = 0) :
    Group.OnCurve d (nativePreimage d codec writer (model.coordinates point)) ∧
      nativeEight d (nativePreimage d codec writer (model.coordinates point)) =
        model.coordinates point := by
  rw [native_preimage_coordinates codec writer d imaginary model nonSquare imaginarySquare two point]
  exact ⟨model.onCurve _,
    (native_eight_coordinates d imaginary model nonSquare imaginarySquare _).trans
      (congrArg model.coordinates (subgroup_eight_preimage point subgroup))⟩

/-- Native RK's subgroup property follows from the independently admitted key
and the named SPEND_AUTH base. Neither the desired RK's subgroup property nor
its preimage is a premise. Nonidentity/public compressed-key admission and the
actual authorization equality rows remain separate obligations. -/
theorem native_authorization_preimage_complete [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (key spendAuth : J) (keySubgroup : Scalar.order • key = 0)
    (baseSubgroup : Scalar.order • spendAuth = 0) (randomizer : F) :
    let rk := GroupNativeAuthorization.nativeAuthorization d writer
      (model.coordinates key) (model.coordinates spendAuth) randomizer
    Group.OnCurve d (nativePreimage d codec writer rk) ∧
      nativeEight d (nativePreimage d codec writer rk) = rk := by
  dsimp only
  rw [GroupNativeAuthorization.native_authorization_coordinates codec writer d imaginary model
    nonSquare imaginarySquare two key spendAuth randomizer]
  have subgroup : Scalar.order • (key + codec.decode randomizer • spendAuth) = 0 := by
    rw [nsmul_add,← mul_nsmul,Nat.mul_comm (codec.decode randomizer) Scalar.order,
      mul_nsmul,keySubgroup,baseSubgroup,nsmul_zero,add_zero]
  exact native_preimage_complete codec writer d imaginary model nonSquare imaginarySquare
    two _ subgroup

set_option pp.all true in
#check @inverse_eight_equation
#print axioms inverse_eight_equation
set_option pp.all true in
#check @inverse_eight_bound
#print axioms inverse_eight_bound
set_option pp.all true in
#check @native_preimage_coordinates
#print axioms native_preimage_coordinates
set_option pp.all true in
#check @subgroup_eight_preimage
#print axioms subgroup_eight_preimage
set_option pp.all true in
#check @native_eight_coordinates
#print axioms native_eight_coordinates
set_option pp.all true in
#check @native_preimage_complete
#print axioms native_preimage_complete
set_option pp.all true in
#check @native_authorization_preimage_complete
#print axioms native_authorization_preimage_complete

end ShielddSecurity.GroupNativeCofactor
