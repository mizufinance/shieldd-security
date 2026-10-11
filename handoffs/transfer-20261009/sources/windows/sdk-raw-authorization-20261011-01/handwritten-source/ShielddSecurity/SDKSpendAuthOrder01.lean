import ShielddSecurity.SDKCodecJoin01
import ShielddSecurity.GroupNativeNonidentity
import ShielddSecurity.SubgroupOrderPrime06

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKSpendAuthOrder01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

theorem sdk_x_nonzero : SDKSpendAuthCertificates01.sdkBase.x ≠ 0 := by
  have odd : SDKSpendAuthCertificates01.sdkBase.x.val % 2 = 1 := by
    rw [SDKCompressedDecoder01.sdk_x_value]
    exact SDKSpendAuthCertificates01.sdk_x_odd
  intro zero
  simp only [zero, ZMod.val_zero, Nat.zero_mod] at odd
  exact Nat.zero_ne_one odd

theorem base_nonzero : SDKSpendAuthSubgroup01.base ≠ 0 := by
  intro zero
  apply sdk_x_nonzero
  rw [← SDKSpendAuthSubgroup01.base_coordinates, zero, model.identity]
  rfl

/-- Certified prime order follows from the actual SDK base's own subgroup
certificate and coordinates, independently of the earlier traced base. -/
theorem base_order : addOrderOf SDKSpendAuthSubgroup01.base = Scalar.order := by
  letI : Fact (Nat.Prime Scalar.order) := ⟨SubgroupOrderPrime06.order_prime⟩
  exact addOrderOf_eq_prime SDKSpendAuthSubgroup01.base_subgroup base_nonzero

theorem canonical_multiple_nonzero (scalar : Nat)
    (positive : 0 < scalar) (bound : scalar < Scalar.order) :
    scalar • SDKSpendAuthSubgroup01.base ≠ 0 := by
  intro zero
  have divides := addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
  rw [base_order] at divides
  exact Nat.not_dvd_of_pos_of_lt positive bound divides

theorem canonical_multiple_subgroup (scalar : Nat) :
    Scalar.order • (scalar • SDKSpendAuthSubgroup01.base) = 0 := by
  rw [smul_comm, SDKSpendAuthSubgroup01.base_subgroup, nsmul_zero]

theorem canonical_multiple_inverse (scalar : Nat)
    (positive : 0 < scalar) (bound : scalar < Scalar.order) :
    (model.coordinates (scalar • SDKSpendAuthSubgroup01.base)).x *
      ((model.coordinates (scalar • SDKSpendAuthSubgroup01.base)).x)⁻¹ = 1 :=
  GroupNativeNonidentity.nonidentity_inverse_coordinates coefficient model
    (scalar • SDKSpendAuthSubgroup01.base) (canonical_multiple_subgroup scalar)
    (canonical_multiple_nonzero scalar positive bound)

end ShielddSecurity.SDKSpendAuthOrder01

set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthOrder01.sdk_x_nonzero
#print axioms ShielddSecurity.SDKSpendAuthOrder01.sdk_x_nonzero
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthOrder01.base_nonzero
#print axioms ShielddSecurity.SDKSpendAuthOrder01.base_nonzero
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthOrder01.base_order
#print axioms ShielddSecurity.SDKSpendAuthOrder01.base_order
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthOrder01.canonical_multiple_nonzero
#print axioms ShielddSecurity.SDKSpendAuthOrder01.canonical_multiple_nonzero
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthOrder01.canonical_multiple_subgroup
#print axioms ShielddSecurity.SDKSpendAuthOrder01.canonical_multiple_subgroup
set_option pp.all true in
#check @ShielddSecurity.SDKSpendAuthOrder01.canonical_multiple_inverse
#print axioms ShielddSecurity.SDKSpendAuthOrder01.canonical_multiple_inverse
