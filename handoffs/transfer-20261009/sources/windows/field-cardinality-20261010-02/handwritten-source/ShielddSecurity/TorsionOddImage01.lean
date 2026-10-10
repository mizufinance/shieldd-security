import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Index

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TorsionOddImage01

variable {J : Type} [AddCommGroup J]

theorem order_sixteen_of_eight_image (point : J)
    (killed : 16 • point = 0) (eightNonzero : 8 • point ≠ 0) :
    addOrderOf point = 16 := by
  apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul (by decide : 0 < 16) killed
  intro prime primeProof divides
  have dividesTwo : prime ∣ 2 := primeProof.dvd_of_dvd_pow
    (by simpa using divides : prime ∣ 2 ^ 4)
  have equal : prime = 2 :=
    (Nat.prime_dvd_prime_iff_eq primeProof Nat.prime_two).mp dividesTwo
  subst prime
  simpa only [show 16 / 2 = 8 from rfl] using eightNonzero

/-- Cauchy's theorem turns an even eight-multiplication image into an actual
order-sixteen point. The concrete curve must independently exclude those points. -/
theorem odd_eight_image [Finite J] (noSixteen : ∀ point : J, addOrderOf point ≠ 16) :
    Nat.card (nsmulAddMonoidHom (α := J) 8).range % 2 = 1 := by
  classical
  let map : J →+ J := nsmulAddMonoidHom 8
  change Nat.card map.range % 2 = 1
  by_contra odd
  have bound := Nat.mod_lt (Nat.card map.range) (by decide : 0 < 2)
  have even : 2 ∣ Nat.card map.range := Nat.dvd_of_mod_eq_zero (by omega)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨image, order⟩ := exists_prime_addOrderOf_dvd_card' (G := map.range) 2 even
  have nonzero : (image : J) ≠ 0 := by
    intro zero
    have equal : image = 0 := Subtype.ext zero
    rw [equal, addOrderOf_zero] at order
    omega
  have killed : 2 • (image : J) = 0 := by
    have annihilates := addOrderOf_nsmul_eq_zero (image : J)
    rw [AddSubgroup.addOrderOf_coe, order] at annihilates
    exact annihilates
  have member := image.property
  change ∃ point : J, 8 • point = (image : J) at member
  obtain ⟨point, imageEq⟩ := member
  have sixteen : 16 • point = 0 := by
    change (8 * 2) • point = 0
    rw [mul_nsmul, imageEq]
    exact killed
  have eightNonzero : 8 • point ≠ 0 := by rw [imageEq]; exact nonzero
  exact noSixteen point (order_sixteen_of_eight_image point sixteen eightNonzero)

end ShielddSecurity.TorsionOddImage01

set_option pp.all true in
#check @ShielddSecurity.TorsionOddImage01.order_sixteen_of_eight_image
#print axioms ShielddSecurity.TorsionOddImage01.order_sixteen_of_eight_image
set_option pp.all true in
#check @ShielddSecurity.TorsionOddImage01.odd_eight_image
#print axioms ShielddSecurity.TorsionOddImage01.odd_eight_image
