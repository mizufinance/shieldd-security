import ShielddSecurity.ShielddNativeEncode
import ShielddSecurity.GroupNativeAuthorization

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeReadPoint

variable {F Raw Encoded : Type} [Field F]

/-- Exact owned native_point two-reader body. A caller's SDK coordinates are
little-endian byte arrays, reversed before AllowZero. Returning none models
the Rust expect failure; canonical-byte laws below prove success. -/
def readPoint (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (x y : GroupByteCodec.Bytes) : Option (ShielddNativePoint.Point Raw) :=
  match ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations primitives)
      .allowZero (GroupByteCodec.reverseBytes x),
    ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations primitives)
      .allowZero (GroupByteCodec.reverseBytes y) with
  | some xValue, some yValue => some ⟨xValue,yValue⟩
  | _, _ => none

theorem read_point_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (x y : GroupByteCodec.Bytes) :
    (readPoint operations primitives x y).map (ShielddNativePoint.pointValue operations) =
      GroupNativeAuthorization.readPoint
        (ShielddScalarReader.decoder (ShielddNativeScalar.readerBackend operations primitives)) x y := by
  let rx := ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations primitives)
    .allowZero (GroupByteCodec.reverseBytes x)
  let ry := ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations primitives)
    .allowZero (GroupByteCodec.reverseBytes y)
  change ((match rx,ry with
      | some xValue,some yValue => some (⟨xValue,yValue⟩ : ShielddNativePoint.Point Raw)
      | _,_ => none).map (ShielddNativePoint.pointValue operations)) =
    (match rx.map (ShielddNativeScalar.value operations),ry.map (ShielddNativeScalar.value operations) with
      | some xValue,some yValue => some (⟨xValue,yValue⟩ : Group.Point F)
      | _,_ => none)
  cases rx <;> cases ry <;> rfl

theorem coordinate_read_value {S : Type}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F)
    (coordinates : S → Group.Point F)
    (bytes : GroupNativeAuthorization.CoordinateBytes codec coordinates) (point : S) :
    (readPoint operations primitives (bytes.x point) (bytes.y point)).map
      (ShielddNativePoint.pointValue operations) = some (coordinates point) := by
  rw [read_point_value]
  exact GroupNativeAuthorization.read_point_coordinates codec
    (ShielddScalarReader.decoder (ShielddNativeScalar.readerBackend operations primitives))
    coordinates bytes point

/-- The exact raw reader has an output; its coordinate meaning is a derived
conclusion. This provides the input embedding needed by raw native multiply,
without a per-witness successful reader or desired-result premise. -/
theorem coordinate_read_succeeds {S : Type}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F)
    (coordinates : S → Group.Point F)
    (bytes : GroupNativeAuthorization.CoordinateBytes codec coordinates) (point : S) :
    ∃ output, readPoint operations primitives (bytes.x point) (bytes.y point) = some output ∧
      ShielddNativePoint.pointValue operations output = coordinates point := by
  have meaning := coordinate_read_value operations primitives codec coordinates bytes point
  cases checked : readPoint operations primitives (bytes.x point) (bytes.y point) with
  | none => simp only [checked,Option.map_none] at meaning; cases meaning
  | some output =>
      refine ⟨output,by simp only [checked],?_⟩
      simp only [checked,Option.map_some,Option.some.injEq] at meaning
      exact meaning

set_option pp.all true in
#check @read_point_value
#print axioms read_point_value
set_option pp.all true in
#check @coordinate_read_value
#print axioms coordinate_read_value
set_option pp.all true in
#check @coordinate_read_succeeds
#print axioms coordinate_read_succeeds

end ShielddSecurity.ShielddNativeReadPoint
