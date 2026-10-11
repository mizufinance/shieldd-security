import ShielddSecurity.ConcreteCofactorModel01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteSubgroupAdmission01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

/-- Independent input admission: a curve equation and multiplication by the
scalar modulus returning the identity. The pinned Jubjub SubgroupPoint decoder
uses this test after curve decoding. Primitive Rust representation, arithmetic,
and byte correspondence remain separate obligations. -/
def Admitted (encoder : GroupByteCodec.BEWrite canonical) (input : Group.Point F) : Prop :=
  Group.OnCurve coefficient input ∧
    GroupNativeMultiply.nativeMultiply coefficient input
      (GroupByteCodec.reader (encoder.encode (Scalar.order : F))) = Group.identityPoint

theorem order_decoded : canonical.decode (Scalar.order : F) = Scalar.order :=
  TransferReduction.decode_canonical_cast canonical Scalar.order (by decide)

theorem modulus_test_iff (encoder : GroupByteCodec.BEWrite canonical) (point : curve.Point) :
    GroupNativeMultiply.nativeMultiply coefficient (model.coordinates point)
      (GroupByteCodec.reader (encoder.encode (Scalar.order : F))) = Group.identityPoint ↔
        Scalar.order • point = 0 := by
  rw [native_reader_coordinates, order_decoded, ← model.identity]
  exact model.injective.eq_iff

theorem admission_sound (encoder : GroupByteCodec.BEWrite canonical) (input : Group.Point F)
    (admission : Admitted encoder input) :
    ∃ point : curve.Point, model.coordinates point = input ∧ Scalar.order • point = 0 := by
  obtain ⟨point, coordinates⟩ := model.covers input admission.1
  refine ⟨point, coordinates, (modulus_test_iff encoder point).mp ?_⟩
  rw [coordinates]
  exact admission.2

theorem admission_complete (encoder : GroupByteCodec.BEWrite canonical) (point : curve.Point)
    (subgroup : Scalar.order • point = 0) : Admitted encoder (model.coordinates point) :=
  ⟨model.onCurve point, (modulus_test_iff encoder point).mpr subgroup⟩

theorem admission_iff_eight_image (encoder : GroupByteCodec.BEWrite canonical)
    (point : curve.Point) :
    Admitted encoder (model.coordinates point) ↔
      ∃ preimage : curve.Point, (8 : Nat) • preimage = point := by
  rw [Admitted, and_iff_right (model.onCurve point), modulus_test_iff,
    subgroup_iff_eight_image]

/-- Input admission discharges the admitted-key subgroup premise of the
mathematical authorization constructor. The fixed traced base is already
proved subgroup-valued. Its equality to SDK SPEND_AUTH stays open. -/
theorem authorization_preimage_from_admission
    (encoder : GroupByteCodec.BEWrite canonical) (input : Group.Point F)
    (admission : Admitted encoder input) (randomizer : F) :
    let rk := GroupNativeAuthorization.nativeAuthorization coefficient encoder input
      (model.coordinates ConcreteClosedCardinality01.base) randomizer
    Group.OnCurve coefficient (GroupNativeCofactor.nativePreimage coefficient canonical encoder rk) ∧
      GroupNativeCofactor.nativeEight coefficient
        (GroupNativeCofactor.nativePreimage coefficient canonical encoder rk) = rk := by
  obtain ⟨point, coordinates, subgroup⟩ := admission_sound encoder input admission
  rw [← coordinates]
  exact traced_base_authorization_preimage_complete encoder point subgroup randomizer

end ShielddSecurity.ConcreteSubgroupAdmission01

set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.Admitted
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.Admitted
set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.order_decoded
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.order_decoded
set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.modulus_test_iff
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.modulus_test_iff
set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.admission_sound
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.admission_sound
set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.admission_complete
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.admission_complete
set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.admission_iff_eight_image
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.admission_iff_eight_image
set_option pp.all true in
#check @ShielddSecurity.ConcreteSubgroupAdmission01.authorization_preimage_from_admission
#print axioms ShielddSecurity.ConcreteSubgroupAdmission01.authorization_preimage_from_admission
