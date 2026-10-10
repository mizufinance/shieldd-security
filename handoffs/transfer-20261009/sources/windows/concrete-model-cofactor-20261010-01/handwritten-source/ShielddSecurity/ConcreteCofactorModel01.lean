import ShielddSecurity.ConcreteStandardCurveModel01
import ShielddSecurity.ConcreteClosedCardinality01
import ShielddSecurity.GroupNativeCofactor

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteCofactorModel01
open ConcreteJubjubField01 ConcretePointTorsion01

/-- The complete Edwards addition model is instantiated by the actual concrete
Mathlib elliptic curve. This definition makes no native SDK representation claim. -/
noncomputable def model : Group.StandardCurveModel curve.Point coefficient := by
  classical
  exact ConcreteStandardCurveModel01.model

theorem global_exponent (point : curve.Point) : (8 * Scalar.order) • point = 0 :=
  ConcreteClosedCardinality01.global_exponent point

theorem traced_base_subgroup : Scalar.order • ConcreteClosedCardinality01.base = 0 := by
  change CurveCardinalityWindow01.scalarModulus • ConcreteClosedCardinality01.base = 0
  rw [← ConcreteClosedCardinality01.base_order]
  exact addOrderOf_nsmul_eq_zero _

/-- The circuit's cofactor relation uses the closed exponent for every curve
point. Only the actual preimage curve test and three addition equations remain
as row-level premises. -/
theorem cofactor_image_annihilated (preimage twice four eight : Group.Point F)
    (valid : Group.OnCurve coefficient preimage)
    (first : twice = Group.affineAdd coefficient preimage preimage)
    (second : four = Group.affineAdd coefficient twice twice)
    (third : eight = Group.affineAdd coefficient four four) :
    ∃ represented : curve.Point, model.coordinates represented = eight ∧
      Scalar.order • represented = 0 :=
  Group.cofactor_image_annihilated coefficient model Scalar.order global_exponent
    preimage twice four eight valid first second third

theorem subgroup_iff_eight_image (point : curve.Point) :
    Scalar.order • point = 0 ↔ ∃ preimage : curve.Point, (8 : Nat) • preimage = point := by
  constructor
  · intro subgroup
    exact ⟨GroupNativeCofactor.inverseEight • point,
      GroupNativeCofactor.subgroup_eight_preimage point subgroup⟩
  · rintro ⟨preimage, equal⟩
    rw [← equal, ← mul_nsmul, Nat.mul_comm]
    exact global_exponent preimage

/-- Only the byte writer's independent primitive contract is supplied here;
the full group model, coefficient facts, and field codec are concrete. -/
theorem native_reader_coordinates (writer : GroupByteCodec.BEWrite canonical)
    (point : curve.Point) (value : F) :
    GroupNativeMultiply.nativeMultiply coefficient (model.coordinates point)
      (GroupByteCodec.reader (writer.encode value)) =
        model.coordinates (canonical.decode value • point) :=
  GroupByteCodec.native_reader_coordinates canonical writer coefficient imaginary model
    coefficient_no_unit_square imaginary_square two_ne_zero point value

theorem native_preimage_complete (writer : GroupByteCodec.BEWrite canonical)
    (point : curve.Point) (subgroup : Scalar.order • point = 0) :
    Group.OnCurve coefficient
      (GroupNativeCofactor.nativePreimage coefficient canonical writer (model.coordinates point)) ∧
    GroupNativeCofactor.nativeEight coefficient
      (GroupNativeCofactor.nativePreimage coefficient canonical writer (model.coordinates point)) =
        model.coordinates point :=
  GroupNativeCofactor.native_preimage_complete canonical writer coefficient imaginary model
    coefficient_no_unit_square imaginary_square two_ne_zero point subgroup

/-- The previously proved mathematical base discharges the base subgroup
premise. Its equality to the pinned SDK SPEND_AUTH input remains a separate
representation obligation; the admitted key and byte contracts are explicit. -/
theorem traced_base_authorization_preimage_complete
    (writer : GroupByteCodec.BEWrite canonical) (key : curve.Point)
    (keySubgroup : Scalar.order • key = 0) (randomizer : F) :
    let rk := GroupNativeAuthorization.nativeAuthorization coefficient writer
      (model.coordinates key) (model.coordinates ConcreteClosedCardinality01.base) randomizer
    Group.OnCurve coefficient (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) ∧
      GroupNativeCofactor.nativeEight coefficient
        (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) = rk :=
  GroupNativeCofactor.native_authorization_preimage_complete canonical writer coefficient imaginary model
    coefficient_no_unit_square imaginary_square two_ne_zero key ConcreteClosedCardinality01.base
    keySubgroup traced_base_subgroup randomizer

end ShielddSecurity.ConcreteCofactorModel01

set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.model
#print axioms ShielddSecurity.ConcreteCofactorModel01.model
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.global_exponent
#print axioms ShielddSecurity.ConcreteCofactorModel01.global_exponent
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.traced_base_subgroup
#print axioms ShielddSecurity.ConcreteCofactorModel01.traced_base_subgroup
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.cofactor_image_annihilated
#print axioms ShielddSecurity.ConcreteCofactorModel01.cofactor_image_annihilated
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.subgroup_iff_eight_image
#print axioms ShielddSecurity.ConcreteCofactorModel01.subgroup_iff_eight_image
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.native_reader_coordinates
#print axioms ShielddSecurity.ConcreteCofactorModel01.native_reader_coordinates
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.native_preimage_complete
#print axioms ShielddSecurity.ConcreteCofactorModel01.native_preimage_complete
set_option pp.all true in
#check @ShielddSecurity.ConcreteCofactorModel01.traced_base_authorization_preimage_complete
#print axioms ShielddSecurity.ConcreteCofactorModel01.traced_base_authorization_preimage_complete
