import ShielddSecurity.GroupNativeSdk
import ShielddSecurity.GroupNativeSubgroupWitness

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupNativeSdkPreimage

open GroupByteCodec

variable {F : Type} [Field F]

/-- Pinned pari::key first reads SDK affine coordinates into the circuit's
native Point<Scalar>. note::constrain_spend then calls that Point's
cofactor_preimage: multiply by scalar.rs INVERSE_EIGHT. This is a circuit-native
scalar operation, not an additional SDK Fr operation. Its exact loop and byte
semantics are supplied by NativeCofactor and ByteCodec. -/
def readPreimage (codec : TransferReduction.CanonicalField F)
    (writer : BEWrite codec) (decoder : BERead (F := F)) (d : F) (x y : Bytes) :
    Option (Group.Point F) :=
  (GroupNativeAuthorization.readPoint decoder x y).map
    (GroupNativeCofactor.nativePreimage d codec writer)

variable {E S R K Q J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

theorem read_preimage_coordinates [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0) (point : S) :
    readPreimage codec writer decoder d (fq.bytes (sdk.x point)) (fq.bytes (sdk.y point)) =
      some (model.coordinates (GroupNativeCofactor.inverseEight • sdk.embed (sdk.promote point))) := by
  unfold readPreimage
  rw [GroupNativeSdk.native_point_read codec decoder sdk point]
  simp only [Option.map_some]
  exact congrArg some (GroupNativeCofactor.native_preimage_coordinates codec writer d imaginary model
    nonSquare imaginarySquare two (sdk.embed (sdk.promote point)))

/-- Compressed admission independently gives subgroup membership and
nonidentity. Reader success and all six native witness constraints follow;
neither a desired preimage nor any circuit-row equation is a premise. Original
allocation/row coverage and SDK/FFI interpretation remain separate boundaries. -/
theorem admitted_native_constraints [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (bytes : Bytes) (point : S) (accepted : GroupNativeSdk.admissionGate sdk bytes = some point) :
    let publicPoint := model.coordinates (sdk.embed (sdk.promote point))
    let preimage := GroupNativeCofactor.nativePreimage d codec writer publicPoint
    let twice := GroupFixedWindows.nativeAdd d preimage preimage
    let four := GroupFixedWindows.nativeAdd d twice twice
    readPreimage codec writer decoder d (fq.bytes (sdk.x point)) (fq.bytes (sdk.y point)) =
        some preimage ∧
      Group.OnCurve d preimage ∧
      GroupNativeSubgroupWitness.DoubleConstraints d preimage ∧
      GroupNativeSubgroupWitness.DoubleConstraints d twice ∧
      GroupNativeSubgroupWitness.DoubleConstraints d four ∧
      GroupNativeCofactor.nativeEight d preimage = publicPoint ∧ publicPoint.x * publicPoint.x⁻¹ = 1 := by
  dsimp only
  have legal := GroupNativeSdk.admission sdk bytes point accepted
  constructor
  · unfold readPreimage
    rw [GroupNativeSdk.native_point_read codec decoder sdk point]
    rfl
  · exact GroupNativeSubgroupWitness.native_subgroup_constraints codec writer d imaginary model
      nonSquare imaginarySquare two (sdk.embed (sdk.promote point)) legal.2.1 legal.2.2

theorem randomized_read_preimage [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (key : K) (scalar : R) (point : S)
    (accepted : GroupNativeSdk.admissionGate sdk (sdk.keyBytes (sdk.randomize key scalar)) = some point) :
    readPreimage codec writer decoder d (fq.bytes (sdk.x point)) (fq.bytes (sdk.y point)) =
      some (model.coordinates (GroupNativeCofactor.inverseEight •
        (sdk.embed (sdk.keyPoint key) + fr.integer scalar • sdk.embed (sdk.promote sdk.generator)))) := by
  have read := read_preimage_coordinates codec writer decoder sdk imaginary nonSquare imaginarySquare two point
  rw [(GroupNativeSdk.randomized_admission sdk key scalar point accepted).1] at read
  exact read

set_option pp.all true in
#check @read_preimage_coordinates
#print axioms read_preimage_coordinates
set_option pp.all true in
#check @admitted_native_constraints
#print axioms admitted_native_constraints
set_option pp.all true in
#check @randomized_read_preimage
#print axioms randomized_read_preimage

end ShielddSecurity.GroupNativeSdkPreimage
