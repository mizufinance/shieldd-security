import ShielddSecurity.ConcreteJubjubField01
import ShielddSecurity.EdwardsWeierstrassEquiv01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteEdwardsParameters01
open ConcreteJubjubField01

def A : F := 40962
def B : F := -40964

theorem coefficient_nonzero : coefficient ≠ 0 := by
  intro zero
  have divides : Scalar.modulus ∣ coefficientNat :=
    (CharP.cast_eq_zero_iff F Scalar.modulus coefficientNat).mp zero
  exact Nat.not_le_of_gt (by decide : coefficientNat < Scalar.modulus)
    (Nat.le_of_dvd (by decide : 0 < coefficientNat) divides)

theorem coefficient_cross : (10241 : F) * coefficient + 10240 = 0 := by
  have cast := congrArg (fun value : Nat => (value : F)) coefficient_integer_equation
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self, mul_zero] at cast
  exact cast

theorem parameterA : A * (1 + coefficient) = 2 * (1 - coefficient) := by
  unfold A
  have equation := coefficient_cross
  linear_combination 4 * equation

theorem parameterB : B * (1 + coefficient) = -4 := by
  unfold B
  have equation := coefficient_cross
  linear_combination -4 * equation

def parameters : EdwardsWeierstrassEquiv01.Parameters F where
  d := coefficient
  imaginary := imaginary
  A := A
  B := B
  two := two_ne_zero
  nonzeroD := coefficient_nonzero
  nonSquare := coefficient_no_unit_square
  imaginarySquare := imaginary_square
  parameterA := parameterA
  parameterB := parameterB

def discriminantNat : Nat := 126851741217147602894808147733973565440
def discriminant : F := 16 * B ^ 6 * (A * A - 4)

theorem discriminant_integer :
    (16 : Int) * (-40964) ^ 6 * (40962 * 40962 - 4) = (discriminantNat : Int) := by decide +kernel

theorem discriminant_positive : 0 < discriminantNat := by decide +kernel
theorem discriminant_bound : discriminantNat < Scalar.modulus := by decide +kernel

theorem discriminant_value : discriminant = (discriminantNat : F) := by
  have cast := congrArg (fun value : Int => (value : F)) discriminant_integer
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast] at cast
  exact cast

theorem discriminant_nonzero : discriminant ≠ 0 := by
  rw [discriminant_value]
  intro zero
  have divides : Scalar.modulus ∣ discriminantNat :=
    (CharP.cast_eq_zero_iff F Scalar.modulus discriminantNat).mp zero
  exact Nat.not_le_of_gt discriminant_bound (Nat.le_of_dvd discriminant_positive divides)

end ShielddSecurity.ConcreteEdwardsParameters01
