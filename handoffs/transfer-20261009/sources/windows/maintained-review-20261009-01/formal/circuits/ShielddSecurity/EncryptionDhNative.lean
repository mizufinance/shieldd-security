import ShielddSecurity.GroupByteCodec
import ShielddSecurity.GroupNativeSubgroupMultiply
import ShielddSecurity.ShielddNativeSdk

set_option maxHeartbeats 200000

namespace ShielddSecurity.EncryptionDhNative

variable {F : Type} [Field F]

/-- encryption.rs calls Point::multiply on the selected affine key. Its
scalar reader is the owned big-endian255-bit reader in group.rs; it does not
reuse a caller-supplied desired output or multiplication trace. -/
def multiply {codec : TransferReduction.CanonicalField F}
    (writer : GroupByteCodec.BEWrite codec) (d : F)
    (base : Group.Point F) (scalar : F) : Group.Point F :=
  GroupNativeMultiply.nativeMultiply d base (GroupByteCodec.reader (writer.encode scalar))

theorem multiply_coordinates [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : J) (scalar : F) :
    multiply writer d (model.coordinates base) scalar =
      model.coordinates (codec.decode scalar • base) :=
  GroupByteCodec.native_reader_coordinates codec writer d imaginary model
    nonSquare imaginarySquare two base scalar

theorem canonical_multiply_coordinates [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : J) (scalar : Nat) (bounded : scalar < Scalar.order) :
    multiply writer d (model.coordinates base) (scalar : F) =
      model.coordinates (scalar • base) := by
  rw [multiply_coordinates codec writer d imaginary model nonSquare imaginarySquare two,
    TransferReduction.decode_canonical_cast codec scalar
      (lt_trans bounded (by decide : Scalar.order < Scalar.modulus))]

def selectedMultiply {codec : TransferReduction.CanonicalField F}
    (writer : GroupByteCodec.BEWrite codec) (d : F)
    (flagged : Bool) (detection payload : Group.Point F) (scalar : F) : Group.Point F :=
  multiply writer d (if flagged then detection else payload) scalar

theorem selected_coordinates [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (flagged : Bool) (detection payload : J)
    (scalar : Nat) (bounded : scalar < Scalar.order) :
    selectedMultiply writer d flagged (model.coordinates detection)
      (model.coordinates payload) (scalar : F) =
      model.coordinates (scalar • (if flagged then detection else payload)) := by
  cases flagged
  · simpa only [selectedMultiply, Bool.false_eq_true, if_false] using
      canonical_multiply_coordinates codec writer d imaginary model nonSquare
        imaginarySquare two payload scalar bounded
  · simpa only [selectedMultiply, if_true] using
      canonical_multiply_coordinates codec writer d imaginary model nonSquare
        imaginarySquare two detection scalar bounded

/-- These are independent input-key admission obligations and the actual
EPK-derived scalar bounds, never nonidentity of the desired DH output. -/
theorem selected_nonzero {J : Type} [AddCommGroup J]
    (standardPrime : Nat.Prime Scalar.order)
    (flagged : Bool) (detection payload : J)
    (detectionSubgroup : Scalar.order • detection = 0) (detectionNonzero : detection ≠ 0)
    (payloadSubgroup : Scalar.order • payload = 0) (payloadNonzero : payload ≠ 0)
    (scalar : Nat) (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    scalar • (if flagged then detection else payload) ≠ 0 := by
  cases flagged
  · exact GroupNativeSubgroupMultiply.canonical_input_multiple_nonzero
      standardPrime payload payloadSubgroup payloadNonzero scalar positive bounded
  · exact GroupNativeSubgroupMultiply.canonical_input_multiple_nonzero
      standardPrime detection detectionSubgroup detectionNonzero scalar positive bounded

theorem selected_inverse {J : Type} [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d)
    (standardPrime : Nat.Prime Scalar.order)
    (flagged : Bool) (detection payload : J)
    (detectionSubgroup : Scalar.order • detection = 0) (detectionNonzero : detection ≠ 0)
    (payloadSubgroup : Scalar.order • payload = 0) (payloadNonzero : payload ≠ 0)
    (scalar : Nat) (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    (model.coordinates (scalar • (if flagged then detection else payload))).x *
      ((model.coordinates (scalar • (if flagged then detection else payload))).x)⁻¹ = 1 := by
  cases flagged
  · exact GroupNativeSubgroupMultiply.canonical_input_multiple_inverse
      d model standardPrime payload payloadSubgroup payloadNonzero scalar positive bounded
  · exact GroupNativeSubgroupMultiply.canonical_input_multiple_inverse
      d model standardPrime detection detectionSubgroup detectionNonzero scalar positive bounded

variable {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Fallible point/scalar readers are retained. The model derives their
success from global codec laws rather than assuming successful witness reads. -/
def sdkProgram {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    {codec : TransferReduction.CanonicalField F} (writer : GroupByteCodec.BEWrite codec)
    (point : S) (scalar : R) : Option (Group.Point F) :=
  match ShielddNativeSdk.nativePoint backend upstream point,
      ShielddNativeSdk.scalar (fq := fq) (fr := fr) backend scalar with
  | some base, some value => some (multiply writer d base value)
  | _, _ => none

theorem sdk_coordinates [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (point : S) (scalar : R) :
    sdkProgram backend upstream writer point scalar =
      some (model.coordinates (fr.integer scalar • upstream.embed (upstream.promote point))) := by
  rw [sdkProgram, ShielddNativeSdk.native_point_read codec backend upstream,
    ShielddNativeSdk.scalar_read (fq := fq) (fr := fr) backend]
  exact congrArg some (canonical_multiply_coordinates codec writer d imaginary model
    nonSquare imaginarySquare two _ _ (fr.bounded scalar))

theorem sdk_multiply_agrees [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (point : S) (scalar : R) :
    sdkProgram backend upstream writer point scalar =
      some (model.coordinates (upstream.embed (upstream.multiply (upstream.promote point) scalar))) := by
  rw [upstream.multiplyEmbedding]
  exact sdk_coordinates codec writer backend upstream imaginary nonSquare imaginarySquare two point scalar

theorem selected_sdk_agrees [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (flagged : Bool) (detection payload : S) (scalar : R) :
    sdkProgram backend upstream writer (if flagged then detection else payload) scalar =
      some (model.coordinates (upstream.embed (upstream.multiply
        (upstream.promote (if flagged then detection else payload)) scalar))) :=
  sdk_multiply_agrees codec writer backend upstream imaginary nonSquare imaginarySquare
    two (if flagged then detection else payload) scalar

set_option pp.all true in
#check @multiply_coordinates
#print axioms multiply_coordinates
set_option pp.all true in
#check @canonical_multiply_coordinates
#print axioms canonical_multiply_coordinates
set_option pp.all true in
#check @selected_coordinates
#print axioms selected_coordinates
set_option pp.all true in
#check @selected_nonzero
#print axioms selected_nonzero
set_option pp.all true in
#check @selected_inverse
#print axioms selected_inverse
set_option pp.all true in
#check @sdk_coordinates
#print axioms sdk_coordinates
set_option pp.all true in
#check @sdk_multiply_agrees
#print axioms sdk_multiply_agrees
set_option pp.all true in
#check @selected_sdk_agrees
#print axioms selected_sdk_agrees

end ShielddSecurity.EncryptionDhNative
