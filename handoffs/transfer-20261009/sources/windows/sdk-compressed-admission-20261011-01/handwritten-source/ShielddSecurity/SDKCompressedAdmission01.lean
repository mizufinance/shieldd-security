import ShielddSecurity.SDKEncodingInjective01
import ShielddSecurity.SDKCodecJoin01
import ShielddSecurity.GroupNativeSubgroupWitness

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace ShielddSecurity.SDKCompressedAdmission01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

attribute [local irreducible] SDKJubjubMultiply01.multiply SDKJubjubMultiply01.encodedBits
  GroupNativeMultiply.nativeMultiply GroupNativeCofactor.nativePreimage
  GroupNativeCofactor.nativeEight GroupNativeAuthorization.nativeAuthorization
  SDKCodecJoin01.sourceMultiply

/-- Mathematical compressed-point gate: curve decoding, encoded input identity,
the exact SDK byte traversal's modulus test and a separate nonidentity test.
Rust primitive decoding/field/array correspondence remains open. -/
def Accepted (bytes : List Nat) (input : Group.Point F) : Prop :=
  Group.OnCurve coefficient input ∧ SDKEncodingInjective01.encode input = bytes ∧
    SDKJubjubExtended01.isIdentity
      (SDKCodecJoin01.sourceMultiply (SDKJubjubExtended01.affine input)
        SDKJubjubMultiply01.modulusBytes) ∧
    ¬SDKJubjubExtended01.isIdentity (SDKJubjubExtended01.affine input)

/-- Native witness arithmetic, preceding independent original-row transport. -/
def WitnessConstraints (writer : GroupByteCodec.BEWrite canonical) (publicPoint : Group.Point F) : Prop :=
  let preimage := GroupNativeCofactor.nativePreimage coefficient canonical writer publicPoint
  let twice := GroupFixedWindows.nativeAdd coefficient preimage preimage
  let four := GroupFixedWindows.nativeAdd coefficient twice twice
  Group.OnCurve coefficient preimage ∧
    GroupNativeSubgroupWitness.DoubleConstraints coefficient preimage ∧
    GroupNativeSubgroupWitness.DoubleConstraints coefficient twice ∧
    GroupNativeSubgroupWitness.DoubleConstraints coefficient four ∧
    GroupNativeCofactor.nativeEight coefficient preimage = publicPoint ∧ publicPoint.x * publicPoint.x⁻¹ = 1

theorem affine_identity_iff (point : curve.Point) :
    SDKJubjubExtended01.isIdentity (SDKJubjubExtended01.affine (model.coordinates point)) ↔
      point = 0 := by
  rw [SDKJubjubExtended01.identity_test_iff _ _
    (SDKJubjubExtended01.affine_represents (model.coordinates point)), ← model.identity]
  exact model.injective.eq_iff

theorem admission_sound (bytes : List Nat) (input : Group.Point F)
    (admission : Accepted bytes input) :
    ∃ point : curve.Point, model.coordinates point = input ∧ Scalar.order • point = 0 ∧ point ≠ 0 := by
  obtain ⟨point, coordinates⟩ := model.covers input admission.1
  have subgroup : Scalar.order • point = 0 := by
    apply (SDKCodecJoin01.source_modulus_test_iff _ point
      (SDKJubjubExtended01.affine_represents (model.coordinates point))).mp
    rw [coordinates]
    exact admission.2.2.1
  have nonidentity : point ≠ 0 := by
    intro zero
    apply admission.2.2.2
    rw [← coordinates]
    exact (affine_identity_iff point).mpr zero
  exact ⟨point, coordinates, subgroup, nonidentity⟩

theorem admission_complete (point : curve.Point)
    (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0) :
    Accepted (SDKEncodingInjective01.encode (model.coordinates point)) (model.coordinates point) := by
  refine ⟨model.onCurve point, rfl, ?_, ?_⟩
  · exact (SDKCodecJoin01.source_modulus_test_iff _ point
      (SDKJubjubExtended01.affine_represents (model.coordinates point))).mpr subgroup
  · exact fun tested => nonidentity ((affine_identity_iff point).mp tested)

theorem admitted_point_unique (bytes : List Nat) (input : Group.Point F)
    (admission : Accepted bytes input) (point : curve.Point)
    (encoded : SDKEncodingInjective01.encode (model.coordinates point) = bytes) :
    input = model.coordinates point :=
  SDKEncodingInjective01.encoding_injective input (model.coordinates point) admission.1
    (model.onCurve point) (admission.2.1.trans encoded.symm)

theorem native_constraints (writer : GroupByteCodec.BEWrite canonical)
    (bytes : List Nat) (input : Group.Point F) (admission : Accepted bytes input) :
    WitnessConstraints writer input := by
  obtain ⟨point, coordinates, subgroup, nonidentity⟩ := admission_sound bytes input admission
  rw [← coordinates]
  exact GroupNativeSubgroupWitness.native_subgroup_constraints canonical writer coefficient imaginary
    model coefficient_no_unit_square imaginary_square two_ne_zero point subgroup nonidentity

theorem randomized_subgroup (bytes : List Nat) (input : Group.Point F)
    (admission : Accepted bytes input) (scalar : Nat) (bound : scalar < 2 ^ 252) :
    ∃ point : curve.Point,
      model.coordinates point = SDKJubjubExtended01.normalize
        (SDKSubgroupAdmission01.randomize input SDKSpendAuthSubgroup01.base scalar) ∧
      Scalar.order • point = 0 := by
  obtain ⟨key, coordinates, subgroup, _⟩ := admission_sound bytes input admission
  refine ⟨key + scalar • SDKSpendAuthSubgroup01.base, ?_, ?_⟩
  · rw [← coordinates, SDKSubgroupAdmission01.randomize_coordinates key _ scalar bound]
  · rw [nsmul_add, subgroup, smul_comm Scalar.order scalar,
      SDKSpendAuthSubgroup01.base_subgroup, nsmul_zero, zero_add]

theorem randomized_native_agreement (writer : GroupByteCodec.BEWrite canonical)
    (key : curve.Point) (scalar : Nat) (bound : scalar < Scalar.order) :
    GroupNativeAuthorization.nativeAuthorization coefficient writer (model.coordinates key)
      SDKSpendAuthCertificates01.sdkBase (scalar : F) =
    SDKJubjubExtended01.normalize
      (SDKSubgroupAdmission01.randomize (model.coordinates key) SDKSpendAuthSubgroup01.base scalar) := by
  have fieldBound : scalar < Scalar.modulus := lt_trans bound (by decide)
  have width := lt_trans bound GroupScalarCodec.scalar_order_width
  rw [← SDKSpendAuthSubgroup01.base_coordinates,
    GroupNativeAuthorization.native_authorization_coordinates canonical writer coefficient imaginary
      model coefficient_no_unit_square imaginary_square two_ne_zero,
    TransferReduction.decode_canonical_cast canonical scalar fieldBound,
    SDKSubgroupAdmission01.randomize_coordinates key SDKSpendAuthSubgroup01.base scalar width]

/-- Randomization may cancel the input key. The independent output identity
gate is required; input nonidentity alone does not establish the x inverse. -/
theorem randomized_native_constraints (writer : GroupByteCodec.BEWrite canonical)
    (bytes : List Nat) (input : Group.Point F) (admission : Accepted bytes input)
    (scalar : Nat) (bound : scalar < 2 ^ 252)
    (outputGate : ¬SDKJubjubExtended01.isIdentity
      (SDKJubjubExtended01.affine (SDKJubjubExtended01.normalize
        (SDKSubgroupAdmission01.randomize input SDKSpendAuthSubgroup01.base scalar)))) :
    WitnessConstraints writer (SDKJubjubExtended01.normalize
      (SDKSubgroupAdmission01.randomize input SDKSpendAuthSubgroup01.base scalar)) := by
  obtain ⟨point, coordinates, subgroup⟩ := randomized_subgroup bytes input admission scalar bound
  have nonidentity : point ≠ 0 := by
    intro zero
    apply outputGate
    rw [← coordinates]
    exact (affine_identity_iff point).mpr zero
  rw [← coordinates]
  exact GroupNativeSubgroupWitness.native_subgroup_constraints canonical writer coefficient imaginary
    model coefficient_no_unit_square imaginary_square two_ne_zero point subgroup nonidentity

end ShielddSecurity.SDKCompressedAdmission01



set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.Accepted
#print axioms ShielddSecurity.SDKCompressedAdmission01.Accepted
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.WitnessConstraints
#print axioms ShielddSecurity.SDKCompressedAdmission01.WitnessConstraints
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.affine_identity_iff
#print axioms ShielddSecurity.SDKCompressedAdmission01.affine_identity_iff
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.admission_sound
#print axioms ShielddSecurity.SDKCompressedAdmission01.admission_sound
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.admission_complete
#print axioms ShielddSecurity.SDKCompressedAdmission01.admission_complete
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.admitted_point_unique
#print axioms ShielddSecurity.SDKCompressedAdmission01.admitted_point_unique
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.native_constraints
#print axioms ShielddSecurity.SDKCompressedAdmission01.native_constraints
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.randomized_subgroup
#print axioms ShielddSecurity.SDKCompressedAdmission01.randomized_subgroup
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.randomized_native_agreement
#print axioms ShielddSecurity.SDKCompressedAdmission01.randomized_native_agreement
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedAdmission01.randomized_native_constraints
#print axioms ShielddSecurity.SDKCompressedAdmission01.randomized_native_constraints
