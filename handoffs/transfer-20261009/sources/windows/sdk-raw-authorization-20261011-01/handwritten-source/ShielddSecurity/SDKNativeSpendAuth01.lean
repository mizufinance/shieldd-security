import ShielddSecurity.SDKSpendAuthOrder01
import ShielddSecurity.SDKCompressedAdmission01
import ShielddSecurity.ShielddNativeSdk

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace ShielddSecurity.SDKNativeSpendAuth01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

variable {E S R K Q Signing : Type}
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}

/-- Global coordinates of the upstream standard SpendAuth constant. Exact
order is derived from the independently certified SDK mathematical base.
The primitive Rust representation correspondence is still an explicit boundary. -/
structure StandardCoordinates
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing curve.Point fq fr coefficient model) : Prop where
  affineX : fq.integer (upstream.affine upstream.spendAuth).1 =
    4139425550610461525665941076812662132363359224232624900223172373014329534291
  affineY : fq.integer (upstream.affine upstream.spendAuth).2 =
    39635691377166599497441725607757882405510648532010642268690928210480481875248

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing curve.Point fq fr coefficient model)
  (standard : StandardCoordinates upstream)

attribute [local irreducible] SDKJubjubMultiply01.multiply SDKJubjubMultiply01.encodedBits
  GroupNativeMultiply.nativeMultiply GroupNativeCofactor.nativePreimage
  GroupNativeCofactor.nativeEight GroupNativeAuthorization.nativeAuthorization

theorem native_coefficient : coefficient = -(10240 : F) * (10241 : F)⁻¹ := by
  simpa only [div_eq_mul_inv] using coefficient_formula

include standard in
theorem generator_point :
    upstream.embed (upstream.promote upstream.spendAuthSubgroup) = SDKSpendAuthSubgroup01.base := by
  apply model.injective
  rw [upstream.spendAuthEmbedding, upstream.affineMeaning,
    standard.affineX, standard.affineY, SDKSpendAuthSubgroup01.base_coordinates]
  rfl

include standard in
theorem generator_order :
    addOrderOf (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) = Scalar.order := by
  rw [generator_point upstream standard]
  exact SDKSpendAuthOrder01.base_order

include standard in
theorem generator_nonidentity :
    upstream.embed (upstream.promote upstream.spendAuthSubgroup) ≠ 0 := by
  rw [generator_point upstream standard]
  exact SDKSpendAuthOrder01.base_nonzero

include standard in
theorem generator_read {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) :
    (match ShielddNativeSdk.spendAuthProgram upstream with
      | some point => ShielddNativeSdk.nativePoint backend upstream point
      | none => none) = some SDKSpendAuthCertificates01.sdkBase := by
  rw [ShielddNativeSdk.spend_auth_program upstream]
  dsimp only
  rw [ShielddNativeSdk.native_point_read canonical backend upstream,
    generator_point upstream standard, SDKSpendAuthSubgroup01.base_coordinates]

theorem generator_admission :
    SDKCompressedAdmission01.Accepted
      (SDKEncodingInjective01.encode SDKSpendAuthCertificates01.sdkBase)
      SDKSpendAuthCertificates01.sdkBase := by
  rw [← SDKSpendAuthSubgroup01.base_coordinates]
  exact SDKCompressedAdmission01.admission_complete SDKSpendAuthSubgroup01.base
    SDKSpendAuthSubgroup01.base_subgroup SDKSpendAuthOrder01.base_nonzero

include standard in
theorem canonical_multiple_nonzero (scalar : Nat)
    (positive : 0 < scalar) (bound : scalar < Scalar.order) :
    scalar • upstream.embed (upstream.promote upstream.spendAuthSubgroup) ≠ 0 := by
  rw [generator_point upstream standard]
  exact SDKSpendAuthOrder01.canonical_multiple_nonzero scalar positive bound

include standard in
theorem canonical_multiple_inverse (scalar : Nat)
    (positive : 0 < scalar) (bound : scalar < Scalar.order) :
    (model.coordinates (scalar • upstream.embed (upstream.promote upstream.spendAuthSubgroup))).x *
      ((model.coordinates (scalar • upstream.embed (upstream.promote upstream.spendAuthSubgroup))).x)⁻¹ = 1 := by
  rw [generator_point upstream standard]
  exact SDKSpendAuthOrder01.canonical_multiple_inverse scalar positive bound

include standard in
theorem production_randomization (verification : K) (randomizer : R) :
    model.coordinates (upstream.embed (upstream.keyPoint
      (ShielddNativeSdk.planRk upstream verification randomizer))) =
    SDKJubjubExtended01.normalize (SDKSubgroupAdmission01.randomize
      (model.coordinates (upstream.embed (upstream.keyPoint verification)))
      SDKSpendAuthSubgroup01.base (fr.integer randomizer)) := by
  rw [ShielddNativeSdk.plan_randomization upstream verification randomizer,
    generator_point upstream standard,
    SDKSubgroupAdmission01.randomize_coordinates]
  exact lt_trans (fr.bounded randomizer) GroupScalarCodec.scalar_order_width

include standard in
theorem production_native_agreement (writer : GroupByteCodec.BEWrite canonical)
    (verification : K) (randomizer : R) :
    GroupNativeAuthorization.nativeAuthorization coefficient writer
      (model.coordinates (upstream.embed (upstream.keyPoint verification)))
      SDKSpendAuthCertificates01.sdkBase (fr.integer randomizer : F) =
    model.coordinates (upstream.embed (upstream.keyPoint
      (ShielddNativeSdk.planRk upstream verification randomizer))) := by
  rw [production_randomization upstream standard verification randomizer]
  exact SDKCompressedAdmission01.randomized_native_agreement writer
    (upstream.embed (upstream.keyPoint verification)) (fr.integer randomizer) (fr.bounded randomizer)

theorem production_native_constraints (writer : GroupByteCodec.BEWrite canonical)
    (verification : K) (randomizer : R) (point : S)
    (accepted : ShielddNativeSdk.nonidentity upstream
      (upstream.keyBytes (ShielddNativeSdk.planRk upstream verification randomizer)) = some point) :
    SDKCompressedAdmission01.WitnessConstraints writer
      (model.coordinates (upstream.embed (upstream.keyPoint
        (ShielddNativeSdk.planRk upstream verification randomizer)))) := by
  have legal := GroupNativeSdk.admitted_key (ShielddNativeSdk.sdk upstream)
    (ShielddNativeSdk.planRk upstream verification randomizer) point accepted
  exact GroupNativeSubgroupWitness.native_subgroup_constraints canonical writer coefficient imaginary model
    coefficient_no_unit_square imaginary_square two_ne_zero _ legal.2.1 legal.2.2

end ShielddSecurity.SDKNativeSpendAuth01

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.StandardCoordinates
#print axioms ShielddSecurity.SDKNativeSpendAuth01.StandardCoordinates

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.native_coefficient
#print axioms ShielddSecurity.SDKNativeSpendAuth01.native_coefficient

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.generator_point
#print axioms ShielddSecurity.SDKNativeSpendAuth01.generator_point

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.generator_order
#print axioms ShielddSecurity.SDKNativeSpendAuth01.generator_order

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.generator_nonidentity
#print axioms ShielddSecurity.SDKNativeSpendAuth01.generator_nonidentity

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.generator_read
#print axioms ShielddSecurity.SDKNativeSpendAuth01.generator_read

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.generator_admission
#print axioms ShielddSecurity.SDKNativeSpendAuth01.generator_admission

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.canonical_multiple_nonzero
#print axioms ShielddSecurity.SDKNativeSpendAuth01.canonical_multiple_nonzero

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.canonical_multiple_inverse
#print axioms ShielddSecurity.SDKNativeSpendAuth01.canonical_multiple_inverse

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.production_randomization
#print axioms ShielddSecurity.SDKNativeSpendAuth01.production_randomization

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.production_native_agreement
#print axioms ShielddSecurity.SDKNativeSpendAuth01.production_native_agreement

set_option pp.all true in
#check @ShielddSecurity.SDKNativeSpendAuth01.production_native_constraints
#print axioms ShielddSecurity.SDKNativeSpendAuth01.production_native_constraints
