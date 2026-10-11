import ShielddSecurity.ShielddNativeReadPoint
import ShielddSecurity.ShielddNativeSdk

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeSdkRaw

open GroupByteCodec

variable {F Raw Encoded : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Owned circuits/encoding.rs reader, returning the raw Scalar wrapper used
by the native arithmetic. The same operations interpretation is used by its
constructed AllowZero reader and by Point/Extended arithmetic. -/
def field (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (value : Q) :
    Option (ShielddNativeScalar.Wrapped Raw) :=
  ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations primitives)
    .allowZero (reverseBytes (fq.bytes value))

/-- Exact pari::scalar Fr LE bytes→Fq parse→owned field reader; no cast or
per-input scalar interpretation is substituted for this source program. -/
def scalar (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (value : R) :
    Option (ShielddNativeScalar.Wrapped Raw) :=
  match fq.parse (fr.bytes value) with
  | some embedded => field (fq := fq) operations primitives embedded
  | none => none

def nativePoint (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) (point : S) :
    Option (ShielddNativePoint.Point Raw) :=
  ShielddNativeReadPoint.readPoint operations primitives
    (fq.bytes (ShielddNativeSdk.coordinateX upstream point))
    (fq.bytes (ShielddNativeSdk.coordinateY upstream point))

def key (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) (verification : K) :
    Option (ShielddNativePoint.Point Raw) :=
  match ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) with
  | some point => nativePoint operations primitives upstream point
  | none => none

def generator (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) :
    Option (ShielddNativePoint.Point Raw) :=
  match ShielddNativeSdk.spendAuthProgram upstream with
  | some point => nativePoint operations primitives upstream point
  | none => none

theorem field_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (value : Q) :
    (field (fq := fq) operations primitives value).map (ShielddNativeScalar.value operations) =
      ShielddNativeSdk.field (fq := fq) (ShielddNativeScalar.readerBackend operations primitives) value := rfl

theorem scalar_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (value : R) :
    (scalar (fq := fq) (fr := fr) operations primitives value).map
        (ShielddNativeScalar.value operations) =
      ShielddNativeSdk.scalar (fq := fq) (fr := fr)
        (ShielddNativeScalar.readerBackend operations primitives) value := by
  unfold scalar ShielddNativeSdk.scalar
  cases parsed : fq.parse (fr.bytes value) <;> rfl

theorem native_point_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) (point : S) :
    (nativePoint operations primitives upstream point).map (ShielddNativePoint.pointValue operations) =
      ShielddNativeSdk.nativePoint (ShielddNativeScalar.readerBackend operations primitives) upstream point :=
  ShielddNativeReadPoint.read_point_value operations primitives _ _

theorem key_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) (verification : K) :
    (key operations primitives upstream verification).map (ShielddNativePoint.pointValue operations) =
      ShielddNativeSdk.key (ShielddNativeScalar.readerBackend operations primitives) upstream verification := by
  unfold key ShielddNativeSdk.key
  cases checked : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) with
  | none => rfl
  | some point => exact native_point_value operations primitives upstream point

theorem generator_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) :
    (generator operations primitives upstream).map (ShielddNativePoint.pointValue operations) =
      (match ShielddNativeSdk.spendAuthProgram upstream with
      | some point => ShielddNativeSdk.nativePoint (ShielddNativeScalar.readerBackend operations primitives)
          upstream point
      | none => none) := by
  unfold generator
  cases checked : ShielddNativeSdk.spendAuthProgram upstream with
  | none => rfl
  | some point => exact native_point_value operations primitives upstream point

set_option pp.all true in
#check @field_value
#print axioms field_value
set_option pp.all true in
#check @scalar_value
#print axioms scalar_value
set_option pp.all true in
#check @native_point_value
#print axioms native_point_value
set_option pp.all true in
#check @key_value
#print axioms key_value
set_option pp.all true in
#check @generator_value
#print axioms generator_value

end ShielddSecurity.ShielddNativeSdkRaw
