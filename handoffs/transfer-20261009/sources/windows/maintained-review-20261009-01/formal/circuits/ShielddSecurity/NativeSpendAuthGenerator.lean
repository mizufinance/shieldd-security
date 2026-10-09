import ShielddSecurity.ShielddNativeSdkRaw
import ShielddSecurity.GroupNativeGenerator

set_option maxHeartbeats 150000

namespace ShielddSecurity.NativeSpendAuthGenerator

variable {F : Type} [Field F]

def literal : Group.Point F :=
  ⟨4139425550610461525665941076812662132363359224232624900223172373014329534291,
    39635691377166599497441725607757882405510648532010642268690928210480481875248⟩

variable {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Explicit standard RedJubjub SpendAuth interpretation, for the fixed
upstream basepoint rather than a Transfer witness. The coordinates identify
reddsa 0.5.2 SPENDAUTHSIG_BASEPOINT_BYTES after Jubjub decoding; the exact order
is a standard curve fact. Neither the owned scalar-one constructor nor the
owned reverse/AllowZero reader is supplied by this contract. -/
structure StandardSpendAuth
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) : Prop where
  affineX : fq.integer (upstream.affine upstream.spendAuth).1 =
    4139425550610461525665941076812662132363359224232624900223172373014329534291
  affineY : fq.integer (upstream.affine upstream.spendAuth).2 =
    39635691377166599497441725607757882405510648532010642268690928210480481875248
  exactOrder : addOrderOf (upstream.embed upstream.spendAuth) = Scalar.order

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
  (standard : StandardSpendAuth upstream)

theorem generator_coordinates :
    model.coordinates (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) =
      (literal : Group.Point F) := by
  rw [upstream.spendAuthEmbedding, upstream.affineMeaning,
    standard.affineX, standard.affineY]
  rfl

theorem generator_order :
    addOrderOf (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) = Scalar.order := by
  rw [upstream.spendAuthEmbedding]
  exact standard.exactOrder

/-- Both owned fallible parsers succeed before the circuit coordinate reader
runs. Success follows from the globally quantified upstream API laws. -/
theorem generator_read [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) :
    (match ShielddNativeSdk.spendAuthProgram upstream with
      | some point => ShielddNativeSdk.nativePoint backend upstream point
      | none => none) = some (literal : Group.Point F) := by
  rw [ShielddNativeSdk.spend_auth_program upstream]
  rw [ShielddNativeSdk.native_point_read codec backend upstream]
  rw [generator_coordinates upstream standard]

theorem raw_generator_read [CharP F Scalar.modulus] {Raw Encoded : Type}
    (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) :
    (ShielddNativeSdkRaw.generator operations primitives upstream).map
      (ShielddNativePoint.pointValue operations) = some (literal : Group.Point F) := by
  rw [ShielddNativeSdkRaw.generator_value]
  exact generator_read upstream standard codec
    (ShielddNativeScalar.readerBackend operations primitives)

theorem canonical_multiple_nonzero (scalar : Nat)
    (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    scalar • upstream.embed (upstream.promote upstream.spendAuthSubgroup) ≠ 0 :=
  GroupNativeGenerator.canonical_multiple_nonzero _ (generator_order upstream standard)
    scalar positive bounded

theorem canonical_multiple_inverse (scalar : Nat)
    (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    (model.coordinates (scalar • upstream.embed (upstream.promote upstream.spendAuthSubgroup))).x *
      ((model.coordinates (scalar • upstream.embed (upstream.promote upstream.spendAuthSubgroup))).x)⁻¹ = 1 :=
  GroupNativeGenerator.canonical_multiple_inverse d model _ (generator_order upstream standard)
    scalar positive bounded

set_option pp.all true in
#check @generator_coordinates
#print axioms generator_coordinates
set_option pp.all true in
#check @generator_order
#print axioms generator_order
set_option pp.all true in
#check @generator_read
#print axioms generator_read
set_option pp.all true in
#check @raw_generator_read
#print axioms raw_generator_read
set_option pp.all true in
#check @canonical_multiple_nonzero
#print axioms canonical_multiple_nonzero
set_option pp.all true in
#check @canonical_multiple_inverse
#print axioms canonical_multiple_inverse

end ShielddSecurity.NativeSpendAuthGenerator
