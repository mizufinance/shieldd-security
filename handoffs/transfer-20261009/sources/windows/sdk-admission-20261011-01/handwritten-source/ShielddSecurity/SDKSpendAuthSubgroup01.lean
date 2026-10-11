import ShielddSecurity.SDKSpendAuthCertificates01
import ShielddSecurity.SDKSubgroupAdmission01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace ShielddSecurity.SDKSpendAuthSubgroup01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

attribute [local irreducible] SDKJubjubMultiply01.multiply SDKJubjubMultiply01.encodedBits
  GroupNativeMultiply.nativeMultiply GroupNativeCofactor.nativePreimage
  GroupNativeCofactor.nativeEight GroupNativeAuthorization.nativeAuthorization

/-- The concrete point selected by the independently certified SDK compressed
constant's mathematical Edwards coordinates. Native decoder correspondence
is separate. This point is not defined by equality to the old traced base. -/
noncomputable def base : curve.Point :=
  Classical.choose (model.covers SDKSpendAuthCertificates01.sdkBase
    SDKSpendAuthCertificates01.sdkBase_on_curve)

theorem base_coordinates : model.coordinates base = SDKSpendAuthCertificates01.sdkBase :=
  Classical.choose_spec (model.covers SDKSpendAuthCertificates01.sdkBase
    SDKSpendAuthCertificates01.sdkBase_on_curve)

/-- Three certified doublings discharge SDK-base subgroup membership using
the closed global exponent, without tracing an unrolled scalar-order walk. -/
theorem base_subgroup : Scalar.order • base = 0 := by
  obtain ⟨point, coordinates, subgroup⟩ := cofactor_image_annihilated
    SDKSpendAuthCertificates01.preimage SDKSpendAuthCertificates01.twice
    SDKSpendAuthCertificates01.four SDKSpendAuthCertificates01.sdkBase
    SDKSpendAuthCertificates01.preimage_on_curve SDKSpendAuthCertificates01.preimage_double
    SDKSpendAuthCertificates01.twice_double SDKSpendAuthCertificates01.four_double
  have equal : point = base := model.injective (coordinates.trans base_coordinates.symm)
  rw [← equal]
  exact subgroup

theorem authorization_preimage_complete (writer : GroupByteCodec.BEWrite canonical)
    (input : Group.Point F) (admission : SDKSubgroupAdmission01.Admitted input) (randomizer : F) :
    let rk := GroupNativeAuthorization.nativeAuthorization coefficient writer input
      SDKSpendAuthCertificates01.sdkBase randomizer
    Group.OnCurve coefficient (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) ∧
      GroupNativeCofactor.nativeEight coefficient
        (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) = rk := by
  obtain ⟨key, coordinates, subgroup⟩ := SDKSubgroupAdmission01.admission_sound input admission
  rw [← coordinates, ← base_coordinates]
  exact GroupNativeCofactor.native_authorization_preimage_complete canonical writer coefficient imaginary model
    coefficient_no_unit_square imaginary_square two_ne_zero key base subgroup base_subgroup randomizer

theorem randomized_preimage_complete (writer : GroupByteCodec.BEWrite canonical)
    (input : Group.Point F) (admission : SDKSubgroupAdmission01.Admitted input)
    (scalar : Nat) (bound : scalar < 2 ^ 252) :
    let rk := SDKJubjubExtended01.normalize (SDKSubgroupAdmission01.randomize input base scalar)
    Group.OnCurve coefficient (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) ∧
      GroupNativeCofactor.nativeEight coefficient
        (GroupNativeCofactor.nativePreimage coefficient canonical writer rk) = rk := by
  obtain ⟨key, coordinates, subgroup⟩ := SDKSubgroupAdmission01.admission_sound input admission
  have baseMultiple : Scalar.order • (scalar • base) = 0 := by
    rw [smul_comm, base_subgroup, nsmul_zero]
  have keySubgroup : Scalar.order • (key + scalar • base) = 0 := by
    rw [nsmul_add, subgroup, baseMultiple, zero_add]
  dsimp only
  rw [← coordinates, SDKSubgroupAdmission01.randomize_coordinates key base scalar bound]
  exact native_preimage_complete writer _ keySubgroup

end ShielddSecurity.SDKSpendAuthSubgroup01

set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthSubgroup01.base
#print axioms ShielddSecurity.SDKSpendAuthSubgroup01.base
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthSubgroup01.base_coordinates
#print axioms ShielddSecurity.SDKSpendAuthSubgroup01.base_coordinates
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthSubgroup01.base_subgroup
#print axioms ShielddSecurity.SDKSpendAuthSubgroup01.base_subgroup
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthSubgroup01.authorization_preimage_complete
#print axioms ShielddSecurity.SDKSpendAuthSubgroup01.authorization_preimage_complete
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthSubgroup01.randomized_preimage_complete
#print axioms ShielddSecurity.SDKSpendAuthSubgroup01.randomized_preimage_complete
