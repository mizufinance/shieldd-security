import ShielddSecurity.ShielddNativeFieldHashLoaded
import ShielddSecurity.NativeAssetMap

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.NativeEncryptionFixedKeys

variable {F Q Encoded : Type} [Field F] [DecidableEq F]
  [CharP F Scalar.modulus] [Fintype F]
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
  (fq : GroupNativeSdk.FqBytes Q)
  (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
  (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
  (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
  (codec : TransferReduction.CanonicalField F)

/-- The fixed SDK audit keys hash no operands. Successful table loading and
the exact empty-input permutation are derived from the owned loader proof. -/
def hashObject (domain : Nat) : Q :=
  (ShielddNativeFieldHashLoaded.loadedHash hex fq arithmetic initial square
    domain ([] : List Q)).getD arithmetic.zero

theorem hash_object (domain : Nat) (bounded : domain < 2^64) :
    hashObject hex fq arithmetic initial square domain =
      ShielddNativeRnkHash.hash fq arithmetic initial square codec
        NativeAssetHashParameters.smallParameters
        ShielddNativeFieldHashLoaded.wideParameters domain [] := by
  have bound : ([] : List Q).length * 256 + domain < 2^64 := by simpa using bounded
  unfold hashObject
  rw [ShielddNativeFieldHashLoaded.hash_object hex fq arithmetic initial square codec domain [] bound]
  rfl

include codec in
theorem hash_value (domain : Nat) (bounded : domain < 2^64) :
    NativeAssetMap.value (F := F) fq (hashObject hex fq arithmetic initial square domain) =
      Poseidon.hash3 NativeAssetHashParameters.smallParameters domain [] := by
  rw [hash_object hex fq arithmetic initial square codec domain bounded]
  have bound : ([] : List Q).length * 256 + domain < 2^64 := by simpa using bounded
  have interpreted := ShielddNativeFieldHash.hash_value fq arithmetic initial square codec
    NativeAssetHashParameters.smallParameters ShielddNativeFieldHashLoaded.wideParameters
    domain ([] : List Q) bound
  simpa only [NativeAssetMap.value, ShielddNativeIvkHash.fqValue, List.map_nil,
    Poseidon.hash, List.length_nil, Nat.zero_le, if_true] using interpreted

variable {E S R K Signing J : Type} [AddCommGroup J]
  {fr : GroupNativeSdk.FrBytes R} {d : F} {model : Group.StandardCurveModel J d}
variable (api : ElligatorNativeRoots.SqrtAPI F)
  (ops : NativeAssetMap.Primitives fq api)
  (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
  (points : NativeAssetMap.PointPrimitives fq upstream)

/-- SDK audit::UNREGULATED_DETECTION and audit::UNREGULATED_RING apply the
same owned map to the empty-input domain28 and domain29 hash respectively. -/
def fixedGenerator (domain : Nat) : S :=
  NativeAssetMap.toSubgroup fq api ops points
    (hashObject hex fq arithmetic initial square domain)

def fixedValue (domain : Nat) : Group.Point F :=
  ElligatorNativeProgram.generatorValue codec api NativeAssetMap.coefficientC1
    NativeAssetMap.coefficientC2 NativeAssetMap.coefficientK d
    (Poseidon.hash3 NativeAssetHashParameters.smallParameters domain [])

variable (imaginary : F) (nonSquare : Group.NoUnitSquare d)
  (imaginarySquare : imaginary * imaginary = -1)
  (kNonzero : (NativeAssetMap.coefficientK : F) ≠ 0)
  (denominator : Group.NoUnitSquare (-5 : F))
  (edwards : (NativeAssetMap.coefficientK : F) * d = 40960)
  (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
  (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)

include imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler in
theorem coordinates (domain : Nat) (bounded : domain < 2^64) :
    model.coordinates (upstream.embed (upstream.promote
      (fixedGenerator hex fq arithmetic initial square api ops upstream points domain))) =
      fixedValue (d := d) codec api domain := by
  unfold fixedGenerator
  rw [NativeAssetMap.to_subgroup_coordinates fq api ops upstream points codec
    imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler,
    hash_value hex fq arithmetic initial square codec domain bounded]
  rfl

include hex fq arithmetic initial square ops upstream points imaginary nonSquare
  imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler in
/-- Membership comes from the produced SDK subgroup objects and the exact
pinned upstream contract. No chosen fallback point or subgroup premise is an
argument. Identity is permitted; initialization's nonidentity guard is separate. -/
theorem represented_keys : ∃ detection payload : J,
    model.coordinates detection = fixedValue (d := d) codec api 28 ∧ Scalar.order • detection = 0 ∧
    model.coordinates payload = fixedValue (d := d) codec api 29 ∧ Scalar.order • payload = 0 := by
  refine ⟨upstream.embed (upstream.promote
      (fixedGenerator hex fq arithmetic initial square api ops upstream points 28)),
    upstream.embed (upstream.promote
      (fixedGenerator hex fq arithmetic initial square api ops upstream points 29)),
    coordinates hex fq arithmetic initial square codec api ops upstream points
      imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler
      28 (by decide), upstream.subgroup _,
    coordinates hex fq arithmetic initial square codec api ops upstream points
      imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler
      29 (by decide), upstream.subgroup _⟩

include imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler in
theorem native_point {ByteEncoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) ByteEncoded Native)
    (domain : Nat) (bounded : domain < 2^64) :
    ShielddNativeSdk.nativePoint backend upstream
      (fixedGenerator hex fq arithmetic initial square api ops upstream points domain) =
      some (fixedValue (d := d) codec api domain) := by
  rw [ShielddNativeSdk.native_point_read codec backend upstream,
    coordinates hex fq arithmetic initial square codec api ops upstream points
      imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler domain bounded]

set_option pp.all true in
#check @hash_object
#print axioms hash_object
set_option pp.all true in
#check @hash_value
#print axioms hash_value
set_option pp.all true in
#check @coordinates
#print axioms coordinates
set_option pp.all true in
#check @represented_keys
#print axioms represented_keys
set_option pp.all true in
#check @native_point
#print axioms native_point

end ShielddSecurity.NativeEncryptionFixedKeys
