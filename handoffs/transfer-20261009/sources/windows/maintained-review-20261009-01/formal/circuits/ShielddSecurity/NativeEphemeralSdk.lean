import ShielddSecurity.GroupNativeSdk
import ShielddSecurity.GroupNativeGenerator

set_option maxHeartbeats 180000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEphemeralSdk

open GroupByteCodec
variable {F : Type} [Field F] [CharP F Scalar.modulus]
variable {E S R K Q J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Source path: pari::scalar reads the SDK Fr bytes through canonical Fq;
    group::generator reads that SAME SDK SPEND_AUTH generator's coordinates;
    owned native Point::multiply reads the resulting base-field scalar bytes.
    All codecs and group laws are global interfaces, not a desired EPK result. -/
def readEphemeral (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model) (scalar : R) :
    Option (Group.Point F) :=
  (GroupNativeSdk.readScalar fq fr decoder scalar).bind fun value =>
    (GroupNativeAuthorization.readPoint decoder (fq.bytes (sdk.x sdk.generator))
      (fq.bytes (sdk.y sdk.generator))).map fun base =>
        GroupNativeMultiply.nativeMultiply d base (reader (writer.encode value))

/-- Neither a scalar conversion result nor a generator coordinate value is
    assumed for this caller. Both readers use the same SDK objects/model. -/
theorem scalar_generator_reads (codec : TransferReduction.CanonicalField F)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model) (scalar : R) :
    GroupNativeSdk.readScalar fq fr decoder scalar = some (fr.integer scalar : F) ∧
      codec.decode (fr.integer scalar : F) = fr.integer scalar ∧
      GroupNativeAuthorization.readPoint decoder (fq.bytes (sdk.x sdk.generator))
        (fq.bytes (sdk.y sdk.generator)) = some (model.coordinates (sdk.embed sdk.spendAuth)) := by
  have input := GroupNativeSdk.scalar_canonical codec fq fr decoder scalar
  have base := GroupNativeSdk.native_point_read codec decoder sdk sdk.generator
  rw [GroupNativeSdk.generator_embedding sdk] at base
  exact ⟨input.1,input.2,base⟩

theorem native_epk_coordinates (codec : TransferReduction.CanonicalField F)
    (writer : BEWrite codec) (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0) (scalar : R) :
    readEphemeral codec writer decoder sdk scalar =
      some (model.coordinates (fr.integer scalar • sdk.embed sdk.spendAuth)) := by
  have reads := scalar_generator_reads codec decoder sdk scalar
  unfold readEphemeral
  rw [reads.1,reads.2.2]
  simp only [Option.bind_some,Option.map_some]
  apply congrArg some
  rw [native_reader_coordinates codec writer d imaginary model nonSquare imaginarySquare two,reads.2.1]

/-- Nonzero canonical SDK Fr is an independent lawful input boundary.
    Exact SPEND_AUTH order is a global generator contract. The derived x inverse
    supplies arithmetic legality for actual original-row constructors later;
    no published/computed point, inverse witness or Satisfies premise occurs. -/
theorem native_epk_inverse (codec : TransferReduction.CanonicalField F)
    (writer : BEWrite codec) (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (exactOrder : addOrderOf (sdk.embed sdk.spendAuth) = Scalar.order)
    (scalar : R) (positive : 0 < fr.integer scalar) :
    (readEphemeral codec writer decoder sdk scalar).map (fun point => point.x*point.x⁻¹) = some 1 := by
  rw [native_epk_coordinates codec writer decoder sdk imaginary nonSquare imaginarySquare two]
  simp only [Option.map_some]
  exact congrArg some (GroupNativeGenerator.canonical_multiple_inverse d model
    (sdk.embed sdk.spendAuth) exactOrder (fr.integer scalar) positive (fr.bounded scalar))

theorem native_epk_nonidentity (codec : TransferReduction.CanonicalField F)
    (writer : BEWrite codec) (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (exactOrder : addOrderOf (sdk.embed sdk.spendAuth) = Scalar.order)
    (scalar : R) (positive : 0 < fr.integer scalar) :
    readEphemeral codec writer decoder sdk scalar ≠ some Group.identityPoint := by
  rw [native_epk_coordinates codec writer decoder sdk imaginary nonSquare imaginarySquare two]
  intro same
  have coordinates := Option.some.inj same
  rw [← model.identity] at coordinates
  exact GroupNativeGenerator.canonical_multiple_nonzero (sdk.embed sdk.spendAuth)
    exactOrder (fr.integer scalar) positive (fr.bounded scalar) (model.injective coordinates)

set_option pp.all true in
#check @scalar_generator_reads
#print axioms scalar_generator_reads
set_option pp.all true in
#check @native_epk_coordinates
#print axioms native_epk_coordinates
set_option pp.all true in
#check @native_epk_inverse
#print axioms native_epk_inverse
set_option pp.all true in
#check @native_epk_nonidentity
#print axioms native_epk_nonidentity

end ShielddSecurity.NativeEphemeralSdk