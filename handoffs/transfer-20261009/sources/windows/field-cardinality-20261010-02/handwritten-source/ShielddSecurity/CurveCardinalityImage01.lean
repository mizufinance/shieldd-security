import ShielddSecurity.CurveCardinalityWindow01
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.CurveCardinalityImage01
open CurveCardinalityWindow01

variable {J : Type} [AddGroup J]

theorem kernel_image_cardinality (map : J →+ J) :
    Nat.card J = Nat.card map.ker * Nat.card map.range := by
  rw [← AddSubgroup.index_ker]
  exact (AddSubgroup.card_mul_index map.ker).symm

theorem quotient_is_image (map : J →+ J) (kernelEight : Nat.card map.ker = 8) :
    Nat.card J / 8 = Nat.card map.range := by
  rw [kernel_image_cardinality map, kernelEight]
  omega

theorem eight_scalar_coprime : Nat.Coprime 8 scalarModulus := by decide +kernel

theorem scalar_kernel_divisibility (map : J →+ J) (kernelEight : Nat.card map.ker = 8)
    (base : J) (baseOrder : addOrderOf base = scalarModulus) :
    8 * scalarModulus ∣ Nat.card J := by
  have scalarDivides := addOrderOf_dvd_natCard base
  rw [baseOrder] at scalarDivides
  have eightDivides : 8 ∣ Nat.card J := by
    rw [kernel_image_cardinality map, kernelEight]
    exact dvd_mul_right 8 _
  exact eight_scalar_coprime.mul_dvd_of_dvd_of_dvd eightDivides scalarDivides

/-- The concrete curve must supply the finite type, eight-multiplication map,
kernel cardinality, base-point order, odd image and affine-point upper bound.
This joins those exact obligations without assuming the final cardinality. -/
theorem cardinality_from_image [Finite J] (map : J →+ J)
    (kernelEight : Nat.card map.ker = 8) (base : J)
    (baseOrder : addOrderOf base = scalarModulus)
    (oddImage : Nat.card map.range % 2 = 1)
    (affineBound : Nat.card J ≤ 2 * fieldModulus + 1) :
    Nat.card J = 8 * scalarModulus := by
  letI : Nonempty J := ⟨0⟩
  apply cardinality_from_odd_quotient scalarModulus (Nat.card J) Nat.card_pos
    (scalar_kernel_divisibility map kernelEight base baseOrder)
    (lt_of_le_of_lt affineBound integer_window)
  rw [quotient_is_image map kernelEight]
  exact oddImage

end ShielddSecurity.CurveCardinalityImage01

set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityImage01.kernel_image_cardinality
#print axioms ShielddSecurity.CurveCardinalityImage01.kernel_image_cardinality
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityImage01.quotient_is_image
#print axioms ShielddSecurity.CurveCardinalityImage01.quotient_is_image
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityImage01.eight_scalar_coprime
#print axioms ShielddSecurity.CurveCardinalityImage01.eight_scalar_coprime
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityImage01.scalar_kernel_divisibility
#print axioms ShielddSecurity.CurveCardinalityImage01.scalar_kernel_divisibility
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityImage01.cardinality_from_image
#print axioms ShielddSecurity.CurveCardinalityImage01.cardinality_from_image
