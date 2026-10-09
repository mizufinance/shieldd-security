import ShielddSecurity.ShielddNativeSdkRaw
import ShielddSecurity.ShielddNativeEncode

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeOwnershipMultiply

variable {F Raw Encoded : Type} [Field F] [CharP F Scalar.modulus]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- The native circuit input adapters and Point<Scalar>::multiply share the
same raw arithmetic interpretation. Both adapters are owned source programs;
their successful values follow from the global codecs, rather than premises
about this point or scalar. SDK address association is a separate source join. -/
def multiply (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (sender : S) (scalar : R) : Option (ShielddNativePoint.Point Raw) :=
  match ShielddNativeSdkRaw.nativePoint operations read upstream sender,
      ShielddNativeSdkRaw.scalar (fq := fq) (fr := fr) operations read scalar with
  | some point, some value => some (ShielddNativeEncode.multiplyScalar operations write point value)
  | _, _ => none

theorem scalar_read (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (scalar : R) :
    ∃ value, ShielddNativeSdkRaw.scalar (fq := fq) (fr := fr) operations read scalar = some value ∧
      ShielddNativeScalar.value operations value = (fr.integer scalar : F) := by
  have meaning := ShielddNativeSdkRaw.scalar_value (fq := fq) (fr := fr) operations read scalar
  rw [ShielddNativeSdk.scalar_read] at meaning
  cases observed : ShielddNativeSdkRaw.scalar (fq := fq) (fr := fr) operations read scalar with
  | none => simp only [observed,Option.map_none] at meaning; cases meaning
  | some value =>
      exact ⟨value,rfl,Option.some.inj (by simpa only [observed,Option.map_some] using meaning)⟩

theorem point_read (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) (sender : S) :
    ∃ point, ShielddNativeSdkRaw.nativePoint operations read upstream sender = some point ∧
      ShielddNativePoint.pointValue operations point =
        model.coordinates (upstream.embed (upstream.promote sender)) := by
  have meaning := ShielddNativeSdkRaw.native_point_value operations read upstream sender
  rw [ShielddNativeSdk.native_point_read codec] at meaning
  cases observed : ShielddNativeSdkRaw.nativePoint operations read upstream sender with
  | none => simp only [observed,Option.map_none] at meaning; cases meaning
  | some point =>
      exact ⟨point,rfl,Option.some.inj (by simpa only [observed,Option.map_some] using meaning)⟩

/-- Global standard-coefficient identification is independent of all input
values. The exact Fr LE→Fq→BE input reader and BE writer→255-bit reader are
derived owned programs. The conclusion uses the same native Fr integer. -/
theorem multiply_coordinates (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
    (codec : TransferReduction.CanonicalField F)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (standardCoefficient : d = -(10240 : F) * (10241 : F)⁻¹)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (sender : S) (scalar : R) :
    (multiply operations read write upstream sender scalar).map (ShielddNativePoint.pointValue operations) =
      some (model.coordinates (fr.integer scalar • upstream.embed (upstream.promote sender))) := by
  subst d
  obtain ⟨point,pointRead,pointMeaning⟩ := point_read operations read codec upstream sender
  obtain ⟨value,scalarRead,scalarMeaning⟩ := scalar_read (fq := fq) (fr := fr) operations read scalar
  have canonical : codec.decode (ShielddNativeScalar.value operations value) = fr.integer scalar := by
    rw [scalarMeaning]
    exact TransferReduction.decode_canonical_cast codec _
      (lt_trans (fr.bounded scalar) (by decide : Scalar.order < Scalar.modulus))
  simp only [multiply,pointRead,scalarRead,Option.map_some]
  rw [ShielddNativeEncode.multiply_scalar_coordinates operations write codec imaginary model
    nonSquare imaginarySquare two point (upstream.embed (upstream.promote sender)) pointMeaning value,
    canonical]

set_option pp.all true in
#check @scalar_read
#print axioms scalar_read
set_option pp.all true in
#check @point_read
#print axioms point_read
set_option pp.all true in
#check @multiply_coordinates
#print axioms multiply_coordinates

end ShielddSecurity.ShielddNativeOwnershipMultiply
