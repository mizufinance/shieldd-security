import ShielddSecurity.ConcreteEightTorsionWitness01
import ShielddSecurity.TorsionOddImage01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteNoSixteen01
open TorsionCertifiedField01 ConcretePointTorsion01 ConcreteEightTorsionData01
open ConcreteEightTorsionWitness01

theorem five_negative_three : 5 • point1 = -point3 := by
  apply eq_neg_of_add_eq_zero_left
  rw [← triple_one, ← add_nsmul]
  exact eight_killed

theorem seven_negative_one : 7 • point1 = -point1 := by
  apply eq_neg_of_add_eq_zero_left
  calc
    7 • point1 + point1 = 7 • point1 + 1 • point1 := by rw [one_nsmul]
    _ = 8 • point1 := by rw [← add_nsmul]
    _ = 0 := eight_killed

theorem no_half_negative (target : curve.Point)
    (noHalf : ∀ point : curve.Point, 2 • point ≠ target) (point : curve.Point) :
    2 • point ≠ -target := by
  intro doubled
  apply noHalf (-point)
  rw [nsmul_neg, doubled, neg_neg]

theorem order_eight_indices (point : curve.Point) (order : addOrderOf point = 8) :
    ∃ k : Fin 8, (k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 7) ∧
      k.val • point1 = point := by
  have killed := addOrderOf_nsmul_eq_zero point
  rw [order] at killed
  obtain ⟨k, representation⟩ := eight_torsion_exhaustive point killed
  have fourNonzero : 4 • point ≠ 0 := by
    intro zero
    have divides := addOrderOf_dvd_of_nsmul_eq_zero zero
    rw [order] at divides
    norm_num at divides
  have odd : k.val % 2 ≠ 0 := by
    intro even
    apply fourNonzero
    rw [← representation, ← mul_nsmul]
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    rw [exact_order_eight]
    omega
  exact ⟨k, by have bound := k.isLt; omega, representation⟩

theorem no_half_order_eight (target : curve.Point) (order : addOrderOf target = 8)
    (point : curve.Point) : 2 • point ≠ target := by
  have noFirst : ∀ point : curve.Point, 2 • point ≠ point1 :=
    ConcretePointDoublingSquare01.no_half_first Y1 equation1
  have noThird : ∀ point : curve.Point, 2 • point ≠ point3 :=
    ConcretePointDoublingSquare01.no_half_second Y3 equation3
  obtain ⟨k, indices, representation⟩ := order_eight_indices target order
  rw [← representation]
  rcases indices with first | third | fifth | seventh
  · rw [first, one_nsmul]; exact noFirst point
  · rw [third, triple_one]; exact noThird point
  · rw [fifth, five_negative_three]; exact no_half_negative point3 noThird point
  · rw [seventh, seven_negative_one]; exact no_half_negative point1 noFirst point

theorem no_order_sixteen (point : curve.Point) : addOrderOf point ≠ 16 := by
  intro order
  have doubledOrder : addOrderOf (2 • point) = 8 := by
    rw [addOrderOf_nsmul, order]
    rfl
  exact no_half_order_eight (2 • point) doubledOrder point rfl

theorem odd_eight_image :
    Nat.card (nsmulAddMonoidHom (α := curve.Point) 8).range % 2 = 1 :=
  TorsionOddImage01.odd_eight_image no_order_sixteen

end ShielddSecurity.ConcreteNoSixteen01

set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.five_negative_three
#print axioms ShielddSecurity.ConcreteNoSixteen01.five_negative_three
set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.seven_negative_one
#print axioms ShielddSecurity.ConcreteNoSixteen01.seven_negative_one
set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.no_half_negative
#print axioms ShielddSecurity.ConcreteNoSixteen01.no_half_negative
set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.order_eight_indices
#print axioms ShielddSecurity.ConcreteNoSixteen01.order_eight_indices
set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.no_half_order_eight
#print axioms ShielddSecurity.ConcreteNoSixteen01.no_half_order_eight
set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.no_order_sixteen
#print axioms ShielddSecurity.ConcreteNoSixteen01.no_order_sixteen
set_option pp.all true in
#check @ShielddSecurity.ConcreteNoSixteen01.odd_eight_image
#print axioms ShielddSecurity.ConcreteNoSixteen01.odd_eight_image
