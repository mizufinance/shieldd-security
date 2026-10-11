import ShielddSecurity.ShielddNativeSdkRaw
import ShielddSecurity.ShielddNativeAuthorization

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeAuthorizationRaw

variable {F Raw Encoded : Type} [Field F] [CharP F Scalar.modulus]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Exact owned native authorization body on raw Scalar coordinates. All
reads, the private scalar adapter, byte encoder and Point operations are
defined owned programs, sharing one raw-state interpretation. -/
def authorization (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verification : K) (randomizer : R) : Option (ShielddNativePoint.Point Raw) :=
  match ShielddNativeSdk.spendAuthProgram upstream with
  | some generator =>
      match ShielddNativeSdkRaw.key operations read upstream verification,
          ShielddNativeSdkRaw.nativePoint operations read upstream generator,
          ShielddNativeSdkRaw.scalar (fq := fq) (fr := fr) operations read randomizer with
      | some actionKey, some base, some value =>
          some (ShielddNativePoint.pointAdd operations (ShielddNativeScalar.coefficientD operations)
            actionKey (ShielddNativeEncode.multiplyScalar operations write base value))
      | _, _, _ => none
  | none => none

theorem multiply_scalar_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
    (codec : TransferReduction.CanonicalField F) (base : ShielddNativePoint.Point Raw)
    (scalar : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativePoint.pointValue operations (ShielddNativeEncode.multiplyScalar operations write base scalar) =
      GroupNativeMultiply.nativeMultiply (-(10240 : F) * (10241 : F)⁻¹)
        (ShielddNativePoint.pointValue operations base)
        (GroupByteCodec.reader ((GroupByteCodec.canonicalWrite codec).encode
          (ShielddNativeScalar.value operations scalar))) := by
  unfold ShielddNativeEncode.multiplyScalar
  rw [ShielddNativeMultiply.multiply_value,ShielddNativeScalar.coefficient_d_value,
    ShielddNativeEncode.encoded_reader,GroupByteCodec.reader_join]

/-- A program equation, for every key/scalar. The parameter equality is the
named global standard Jubjub coefficient identity, independent of Transfer
inputs. No successful reader, group output or row satisfaction is a premise.
The already passed production/admission theorems apply to the right side. -/
theorem authorization_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
    (codec : TransferReduction.CanonicalField F)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (standardCoefficient : d = -(10240 : F) * (10241 : F)⁻¹)
    (verification : K) (randomizer : R) :
    (authorization operations read write upstream verification randomizer).map
        (ShielddNativePoint.pointValue operations) =
      ShielddNativeAuthorization.authorization (ShielddNativeScalar.readerBackend operations read)
        upstream codec (GroupByteCodec.canonicalWrite codec) verification randomizer := by
  unfold authorization ShielddNativeAuthorization.authorization
  cases generatorRead : ShielddNativeSdk.spendAuthProgram upstream with
  | none => rfl
  | some generator =>
      dsimp only
      rw [← ShielddNativeSdkRaw.key_value operations read upstream verification,
        ← ShielddNativeSdkRaw.native_point_value operations read upstream generator,
        ← ShielddNativeSdkRaw.scalar_value operations read randomizer]
      cases keyRead : ShielddNativeSdkRaw.key operations read upstream verification <;>
        cases baseRead : ShielddNativeSdkRaw.nativePoint operations read upstream generator <;>
        cases scalarRead : ShielddNativeSdkRaw.scalar (fq := fq) (fr := fr) operations read randomizer <;>
        simp only [Option.map_none,Option.map_some]
      rw [ShielddNativePoint.point_add_value,multiply_scalar_value operations write codec,
        ShielddNativeScalar.coefficient_d_value,standardCoefficient]
      rfl

set_option pp.all true in
#check @multiply_scalar_value
#print axioms multiply_scalar_value
set_option pp.all true in
#check @authorization_value
#print axioms authorization_value

end ShielddSecurity.ShielddNativeAuthorizationRaw
