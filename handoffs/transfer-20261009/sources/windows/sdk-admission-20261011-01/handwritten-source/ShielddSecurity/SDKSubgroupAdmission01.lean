import ShielddSecurity.SDKJubjubMultiply01
import ShielddSecurity.ConcreteSubgroupAdmission01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace ShielddSecurity.SDKSubgroupAdmission01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

attribute [local irreducible] SDKJubjubMultiply01.multiply SDKJubjubMultiply01.encodedBits

/-- Curve decoding and the SDK source model's modulus identity test. Native
curve decoding, field representation and byte interpretation remain separate
primitive refinement obligations. Identity is admitted, as in into_subgroup. -/
def Admitted (input : Group.Point F) : Prop :=
  Group.OnCurve coefficient input ∧
    SDKJubjubExtended01.isIdentity
      (SDKJubjubMultiply01.multiply (SDKJubjubExtended01.affine input)
        (SDKJubjubMultiply01.encodedBits Scalar.order))

theorem modulus_test_iff (point : curve.Point) :
    SDKJubjubExtended01.isIdentity
      (SDKJubjubMultiply01.multiply (SDKJubjubExtended01.affine (model.coordinates point))
        (SDKJubjubMultiply01.encodedBits Scalar.order)) ↔ Scalar.order • point = 0 :=
  SDKJubjubMultiply01.modulus_test_iff _ point
    (SDKJubjubExtended01.affine_represents (model.coordinates point))

theorem admission_sound (input : Group.Point F) (admission : Admitted input) :
    ∃ point : curve.Point, model.coordinates point = input ∧ Scalar.order • point = 0 := by
  obtain ⟨point, coordinates⟩ := model.covers input admission.1
  refine ⟨point, coordinates, (modulus_test_iff point).mp ?_⟩
  rw [coordinates]
  exact admission.2

theorem admission_complete (point : curve.Point) (subgroup : Scalar.order • point = 0) :
    Admitted (model.coordinates point) :=
  ⟨model.onCurve point, (modulus_test_iff point).mpr subgroup⟩

theorem admission_iff_eight_image (point : curve.Point) :
    Admitted (model.coordinates point) ↔ ∃ preimage : curve.Point, (8 : Nat) • preimage = point := by
  rw [Admitted, and_iff_right (model.onCurve point), modulus_test_iff, subgroup_iff_eight_image]

theorem owned_admission (writer : GroupByteCodec.BEWrite canonical)
    (input : Group.Point F) (admission : Admitted input) :
    ConcreteSubgroupAdmission01.Admitted writer input := by
  obtain ⟨point, coordinates, subgroup⟩ := admission_sound input admission
  rw [← coordinates]
  exact ConcreteSubgroupAdmission01.admission_complete writer point subgroup

theorem authorization_preimage_from_admission (writer : GroupByteCodec.BEWrite canonical)
    (input : Group.Point F) (admission : Admitted input) (randomizer : F) :
    let rk := GroupNativeAuthorization.nativeAuthorization coefficient writer input
      (model.coordinates ConcreteClosedCardinality01.base) randomizer
    Group.OnCurve coefficient (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) ∧
      GroupNativeCofactor.nativeEight coefficient
        (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) = rk :=
  ConcreteSubgroupAdmission01.authorization_preimage_from_admission writer input
    (owned_admission writer input admission) randomizer

/-- Exact ExtendedPoint addition randomization source model, using an explicit
mathematical base. SPEND_AUTH equality to the traced base remains open. -/
noncomputable def randomize (input : Group.Point F) (base : curve.Point) (scalar : Nat) :
    SDKJubjubExtended01.Extended F :=
  SDKJubjubExtended01.add coefficient (SDKJubjubExtended01.affine input)
    (SDKJubjubMultiply01.multiply (SDKJubjubExtended01.affine (model.coordinates base))
      (SDKJubjubMultiply01.encodedBits scalar))

theorem randomize_coordinates (point base : curve.Point) (scalar : Nat) (bound : scalar < 2 ^ 252) :
    SDKJubjubExtended01.normalize (randomize (model.coordinates point) base scalar) =
      model.coordinates (point + scalar • base) := by
  have multiplied : SDKJubjubExtended01.Represents
      (SDKJubjubMultiply01.multiply (SDKJubjubExtended01.affine (model.coordinates base))
        (SDKJubjubMultiply01.encodedBits scalar)) (model.coordinates (scalar • base)) := by
    rw [SDKJubjubMultiply01.encoded_reader]
    have represented := SDKJubjubMultiply01.multiply_represents
      (SDKJubjubExtended01.affine (model.coordinates base)) base
      (SDKJubjubExtended01.affine_represents (model.coordinates base))
      (SDKJubjubMultiply01.encodedBits scalar)
    rw [SDKJubjubMultiply01.encoded_reader, GroupScalarCodec.reader_value 252 scalar bound] at represented
    exact represented
  have sumRep := @SDKJubjubExtended01.add_represents F (inferInstance : Field F) coefficient imaginary
    coefficient_no_unit_square imaginary_square two_ne_zero
    (SDKJubjubExtended01.affine (model.coordinates point))
    (SDKJubjubMultiply01.multiply (SDKJubjubExtended01.affine (model.coordinates base))
      (SDKJubjubMultiply01.encodedBits scalar))
    (model.coordinates point) (model.coordinates (scalar • base))
    (SDKJubjubExtended01.affine_represents (model.coordinates point)) multiplied
    (model.onCurve point) (model.onCurve (scalar • base))
  conv_rhs => rw [model.addition]
  exact SDKJubjubExtended01.normalize_represents _ _ sumRep

theorem randomized_preimage_complete (writer : GroupByteCodec.BEWrite canonical)
    (input : Group.Point F) (admission : Admitted input) (scalar : Nat) (bound : scalar < 2 ^ 252) :
    let rk := SDKJubjubExtended01.normalize (randomize input ConcreteClosedCardinality01.base scalar)
    Group.OnCurve coefficient (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) ∧
      GroupNativeCofactor.nativeEight coefficient
        (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) = rk := by
  obtain ⟨point, coordinates, subgroup⟩ := admission_sound input admission
  have baseMultiple : Scalar.order • (scalar • ConcreteClosedCardinality01.base) = 0 := by
    rw [smul_comm, traced_base_subgroup, nsmul_zero]
  have keySubgroup : Scalar.order • (point + scalar • ConcreteClosedCardinality01.base) = 0 := by
    rw [nsmul_add, subgroup, baseMultiple, zero_add]
  dsimp only
  rw [← coordinates, randomize_coordinates point ConcreteClosedCardinality01.base scalar bound]
  exact native_preimage_complete writer _ keySubgroup

end ShielddSecurity.SDKSubgroupAdmission01

set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.Admitted
#print axioms ShielddSecurity.SDKSubgroupAdmission01.Admitted
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.modulus_test_iff
#print axioms ShielddSecurity.SDKSubgroupAdmission01.modulus_test_iff
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.admission_sound
#print axioms ShielddSecurity.SDKSubgroupAdmission01.admission_sound
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.admission_complete
#print axioms ShielddSecurity.SDKSubgroupAdmission01.admission_complete
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.admission_iff_eight_image
#print axioms ShielddSecurity.SDKSubgroupAdmission01.admission_iff_eight_image
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.owned_admission
#print axioms ShielddSecurity.SDKSubgroupAdmission01.owned_admission
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.authorization_preimage_from_admission
#print axioms ShielddSecurity.SDKSubgroupAdmission01.authorization_preimage_from_admission
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.randomize
#print axioms ShielddSecurity.SDKSubgroupAdmission01.randomize
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.randomize_coordinates
#print axioms ShielddSecurity.SDKSubgroupAdmission01.randomize_coordinates
set_option pp.all true in
#check @ShielddSecurity.SDKSubgroupAdmission01.randomized_preimage_complete
#print axioms ShielddSecurity.SDKSubgroupAdmission01.randomized_preimage_complete
