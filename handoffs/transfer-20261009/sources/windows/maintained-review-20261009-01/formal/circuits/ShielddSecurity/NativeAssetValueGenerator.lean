import ShielddSecurity.ShielddNativeSdk

set_option maxHeartbeats 150000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeAssetValueGenerator

variable {F E S R K Q Signing J : Type} [Field F] [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Global functional contracts for the exact pinned, unmodified SDK
poseidon::hash and map::to_subgroup operations. These laws quantify over all
native field inputs, not one requested generator or one Transfer witness.

`hashMeaning` binds domain26, arity1 and the actual native Fq interpretation.
`mapMeaning` must instantiate the independent SDK sqrt/codec map semantics;
the local circuit API is compared through the already proved root interop.
The concrete SDK backend and parameter-object interpretation remain explicit.
No native identity exclusion or per-input desired coordinate is a field. -/
structure HashMapABI
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (hashSpec : F → F) (mapSpec : F → Group.Point F) where
  poseidon : Nat → List Q → Q
  toSubgroup : Q → S
  hashMeaning : ∀ asset : Q,
    (fq.integer (poseidon 26 [asset]) : F) = hashSpec (fq.integer asset : F)
  mapMeaning : ∀ input : Q,
    model.coordinates (upstream.embed (upstream.promote (toSubgroup input))) =
      mapSpec (fq.integer input : F)

/-- core/asset/src/asset/id.rs::Id::value_generator. The owned method calls
the same two native operations in order, with the original asset field only.
There is no retry/remapping step and no assumed resulting native object. -/
def valueGenerator
    {upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model}
    {hashSpec : F → F} {mapSpec : F → Group.Point F}
    (abi : HashMapABI upstream hashSpec mapSpec) (asset : Q) : S :=
  abi.toSubgroup (abi.poseidon 26 [asset])

theorem source_body
    {upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model}
    {hashSpec : F → F} {mapSpec : F → Group.Point F}
    (abi : HashMapABI upstream hashSpec mapSpec) (asset : Q) :
    valueGenerator abi asset = abi.toSubgroup (abi.poseidon 26 [asset]) := rfl

/-- The native object is produced by the owned program. Equality with the
hash/map semantics follows from global backend laws, never an input-specific
`assetPoint = wantedPoint` premise. Identity outputs remain allowed here. -/
theorem coordinates
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    {hashSpec : F → F} {mapSpec : F → Group.Point F}
    (abi : HashMapABI upstream hashSpec mapSpec) (asset : Q) :
    model.coordinates (upstream.embed (upstream.promote (valueGenerator abi asset))) =
      mapSpec (hashSpec (fq.integer asset : F)) := by
  unfold valueGenerator
  rw [abi.mapMeaning,abi.hashMeaning]

/-- Exact owned native_point/encoding field reader on that SAME produced SDK
object. A variable precompute seed must use this object and the corresponding
actual source LCs; arbitrary caller-supplied native points do not get this law. -/
theorem read_point [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    {hashSpec : F → F} {mapSpec : F → Group.Point F}
    (abi : HashMapABI upstream hashSpec mapSpec) (asset : Q) :
    ShielddNativeSdk.nativePoint backend upstream (valueGenerator abi asset) =
      some (mapSpec (hashSpec (fq.integer asset : F))) := by
  rw [ShielddNativeSdk.native_point_read codec backend upstream,
    coordinates upstream abi asset]

set_option pp.all true in
#check @source_body
#print axioms source_body
set_option pp.all true in
#check @coordinates
#print axioms coordinates
set_option pp.all true in
#check @read_point
#print axioms read_point

end ShielddSecurity.NativeAssetValueGenerator
