import ShielddSecurity.ShielddNativeEncode
import ShielddSecurity.ShielddScalarWriter
import ShielddSecurity.NativeSpendAuthGenerator
import ShielddSecurity.NativeTransferAdmission
import ShielddSecurity.RuntimeNativeEncryptionInitializationCoefficients

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferEpkRawNative

variable {F Raw Written ReadEncoded : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]

/-- Construct the new writer interface from the existing primitive contracts.
Canonical from_fr integer agreement follows from boundedness and field value;
it is not an additional BLST assumption. -/
def writerPrimitives (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations) :
    ShielddScalarWriter.Primitives Written Raw codec operations where
  fromFr := primitives.fromFr
  integer := primitives.integer
  bigEndian := primitives.bigEndian
  fromFrMeaning raw := Scalar.canonical_representative_unique (operations.value raw)
    _ _ (primitives.fromFrBounded raw) (codec.bounded _) (primitives.fromFrValue raw) (codec.roundtrip _)
  bigEndianMeaning encoded _ index := primitives.bigEndianMeaning encoded index

theorem writer_bytes (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (scalar : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativeEncode.encode operations primitives scalar =
      (ShielddScalarWriter.writer codec operations read (writerPrimitives codec operations primitives)).encode
        (ShielddNativeScalar.value operations scalar) :=
  ShielddScalarWriter.raw_write_agreement codec operations read
    (writerPrimitives codec operations primitives) scalar

/-- Same raw base and raw scalar, with no point meaning supplied as a
premise. The owned operation/bit/chunk/coefficient expressions reduce to the
field model used by the EPK row constructors. -/
theorem multiply_agreement (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (base : ShielddNativePoint.Point Raw) (scalar : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativePoint.pointValue operations (ShielddNativeEncode.multiplyScalar operations primitives base scalar) =
      NativeTransferAdmission.nativeMultiply codec
        (ShielddScalarWriter.writer codec operations read (writerPrimitives codec operations primitives))
        ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
        (ShielddNativePoint.pointValue operations base) (ShielddNativeScalar.value operations scalar) := by
  have coefficient : -(10240 : F) * (10241 : F)⁻¹ =
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) := by
    simpa only [RuntimeNativeEncryptionInitializationCoefficients.coefficientD,div_eq_mul_inv,
      Int.cast_ofNat] using (RuntimeNativeEncryptionInitializationCoefficients.d_value (F := F))
  unfold ShielddNativeEncode.multiplyScalar NativeTransferAdmission.nativeMultiply
  rw [ShielddNativeMultiply.multiply_value,ShielddNativeScalar.coefficient_d_value,coefficient,writer_bytes]

variable {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)}

def ephemeral (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
    (scalar : ShielddNativeScalar.Wrapped Raw) : Option (ShielddNativePoint.Point Raw) :=
  (ShielddNativeSdkRaw.generator operations read upstream).map
    (fun base => ShielddNativeEncode.multiplyScalar operations primitives base scalar)

/-- Both owned generator readers and raw multiplication are executed in the
model. Their success and operands are derived; no desired base, output,
subgroup membership or per-scalar point nonidentity occurs as an input. -/
theorem ephemeral_value (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
    (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream)
    (scalar : ShielddNativeScalar.Wrapped Raw) :
    (ephemeral operations read primitives upstream scalar).map (ShielddNativePoint.pointValue operations) =
      some (NativeTransferAdmission.nativeMultiply codec
        (ShielddScalarWriter.writer codec operations read (writerPrimitives codec operations primitives))
        ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
        NativeSpendAuthGenerator.literal (ShielddNativeScalar.value operations scalar)) := by
  have generator := NativeSpendAuthGenerator.raw_generator_read upstream standard codec operations read
  cases observed : ShielddNativeSdkRaw.generator operations read upstream with
  | none => simp only [observed,Option.map_none] at generator; cases generator
  | some base =>
      have baseValue : ShielddNativePoint.pointValue operations base = NativeSpendAuthGenerator.literal :=
        Option.some.inj (by simpa only [observed,Option.map_some] using generator)
      simp only [ephemeral,observed,Option.map_some]
      rw [multiply_agreement,baseValue]

set_option pp.all true in
#check @writerPrimitives
#print axioms writerPrimitives
set_option pp.all true in
#check @writer_bytes
#print axioms writer_bytes
set_option pp.all true in
#check @multiply_agreement
#print axioms multiply_agreement
set_option pp.all true in
#check @ephemeral_value
#print axioms ephemeral_value

end ShielddSecurity.TransferEpkRawNative
