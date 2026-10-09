import ShielddSecurity.NativeAssetHashParameters
import ShielddSecurity.NativeAssetMap

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeAssetGeneratorSource

variable {F Q Encoded : Type} [Field F] [DecidableEq F]
  [CharP F Scalar.modulus] [Fintype F]
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
  (fq : GroupNativeSdk.FqBytes Q)
  (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
  (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
  (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
  (codec : TransferReduction.CanonicalField F)

/-- The owned SMALL-table loader produces the exact native hash object.
The fallback is unreachable by the loader proof, rather than a success or
hash-value premise. The source adapter maps Rust lazy table initialization to
this Option loader; initialization failure is not a successful native input. -/
def hashObject (asset : Q) : Q :=
  (NativeAssetHashParameters.assetSource hex fq arithmetic initial square asset).getD arithmetic.zero

theorem hash_object (asset : Q) :
    hashObject hex fq arithmetic initial square asset =
      NativeAssetHash.block fq arithmetic initial square codec
        NativeAssetHashParameters.smallParameters asset := by
  unfold hashObject
  rw [NativeAssetHashParameters.asset_source_object hex fq arithmetic initial square codec asset]
  rfl

variable {E S R K Signing J : Type} [AddCommGroup J]
  {fr : GroupNativeSdk.FrBytes R} {d : F} {model : Group.StandardCurveModel J d}
variable (api : ElligatorNativeRoots.SqrtAPI F)
  (ops : NativeAssetMap.Primitives fq api)
  (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
  (points : NativeAssetMap.PointPrimitives fq upstream)

/-- Id::value_generator's owned call order: domain26 singleton hash, then
map::to_subgroup on that very object. The two arithmetic views must instantiate
the same native Fq operations in the source adapter. This definition has no
caller-supplied point and permits identity outputs. -/
def valueGenerator (asset : Q) : S :=
  NativeAssetMap.toSubgroup fq api ops points
    (hashObject hex fq arithmetic initial square asset)

variable (imaginary : F) (nonSquare : Group.NoUnitSquare d)
  (imaginarySquare : imaginary * imaginary = -1)
  (kNonzero : (NativeAssetMap.coefficientK : F) ≠ 0)
  (denominator : Group.NoUnitSquare (-5 : F))
  (edwards : (NativeAssetMap.coefficientK : F) * d = 40960)
  (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
  (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)

include imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler in
theorem coordinates (asset : Q) :
    model.coordinates (upstream.embed (upstream.promote
      (valueGenerator hex fq arithmetic initial square api ops upstream points asset))) =
      ElligatorNativeProgram.generatorValue codec api
        NativeAssetMap.coefficientC1 NativeAssetMap.coefficientC2 NativeAssetMap.coefficientK d
        (Poseidon.hash3 NativeAssetHashParameters.smallParameters 26 [(fq.integer asset : F)]) := by
  have hashMeaning : NativeAssetMap.value (F := F) fq
      (hashObject hex fq arithmetic initial square asset) =
      Poseidon.hash3 NativeAssetHashParameters.smallParameters 26 [(fq.integer asset : F)] := by
    rw [hash_object hex fq arithmetic initial square codec asset]
    exact NativeAssetHash.block_value fq arithmetic initial square codec
      NativeAssetHashParameters.smallParameters asset
  unfold valueGenerator
  rw [NativeAssetMap.to_subgroup_coordinates fq api ops upstream points codec
    imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler,
    hashMeaning]

include imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler in
/-- The variable-loop base is read from the SAME produced SDK subgroup
object. The global reader/backend/curve contracts remain explicit. There is
no per-input asset point, successful circuit rows, or inverse premise. -/
theorem native_point {ByteEncoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) ByteEncoded Native) (asset : Q) :
    ShielddNativeSdk.nativePoint backend upstream
      (valueGenerator hex fq arithmetic initial square api ops upstream points asset) =
      some (ElligatorNativeProgram.generatorValue codec api
        NativeAssetMap.coefficientC1 NativeAssetMap.coefficientC2 NativeAssetMap.coefficientK d
        (Poseidon.hash3 NativeAssetHashParameters.smallParameters 26 [(fq.integer asset : F)])) := by
  rw [ShielddNativeSdk.native_point_read codec backend upstream,
    coordinates hex fq arithmetic initial square codec api ops upstream points
      imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler asset]

set_option pp.all true in
#check @hash_object
#print axioms hash_object
set_option pp.all true in
#check @coordinates
#print axioms coordinates
set_option pp.all true in
#check @native_point
#print axioms native_point

end ShielddSecurity.NativeAssetGeneratorSource
