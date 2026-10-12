import ShielddSecurity.ConcreteRepresentation274
import ShielddSecurity.ModularPower
import ShielddSecurity.Group
import ShielddSecurity.CapturedFirstSubgroup81
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.OrderOfElement
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ConcreteFieldParameters280
namespace Euler
variable {F : Type} [Field F]
theorem finite_field_power [Fintype F] {p : Nat} (cardinality : Fintype.card F = p)
    (value : F) (nonzero : value ≠ 0) : value ^ (p - 1) = 1 := by
  classical
  rw [← cardinality]
  calc
    _ = (Units.mk0 value nonzero ^ (Fintype.card F - 1) : Fˣ).1 := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    _ = 1 := by rw [← Fintype.card_units, pow_card_eq_one]; rfl

theorem nonsquare_of_euler [Fintype F] {p half : Nat}
    (cardinality : Fintype.card F = p) (twice : half * 2 = p - 1)
    (two : (2 : F) ≠ 0) (d : F) (euler : d ^ half = -1) :
    Group.NoUnitSquare d := by
  intro value unit
  have nonzero : value ≠ 0 := by
    intro zero
    simp only [zero, mul_zero] at unit
    exact zero_ne_one unit
  have fermat := finite_field_power cardinality value nonzero
  have contradiction : (-1 : F) = 1 := by
    calc
      _ = d ^ half * value ^ (half * 2) := by rw [euler, twice, fermat]; ring
      _ = (d * value * value) ^ half := by rw [mul_pow, mul_pow, pow_mul]; ring
      _ = 1 := by rw [unit]; simp
  apply two
  calc
    (2 : F) = 1 - (-1 : F) := by ring
    _ = 0 := by rw [contradiction]; ring

end Euler
abbrev F := ConcreteRepresentation274.F
instance modulusNonzero : NeZero CanonicalFp206.p := ⟨by decide⟩
def coefficientNat : Nat :=
  19257038036680949359750312669786877991949435402254120286184196891950884077233
def coefficient : F := (coefficientNat : F)
def imaginaryNat : Nat := 3465144826073652318776269530687742778270252468765361963008
def imaginary : F := (imaginaryNat : F)
def half : Nat := 26217937587563095239723870254092982918845276250263818911301829349969290592256

theorem two_ne_zero : (2 : F) ≠ 0 := by
  intro zero
  have divides : CanonicalFp206.p ∣ 2 :=
    (CharP.cast_eq_zero_iff F CanonicalFp206.p 2).mp (by simpa only [Nat.cast_ofNat] using zero)
  exact Nat.not_le_of_gt (by decide : 2 < CanonicalFp206.p)
    (Nat.le_of_dvd (by decide : 0 < 2) divides)

theorem imaginary_integer_equation :
    imaginaryNat * imaginaryNat + 1 =
      228988810152649578064853576960394133505 * CanonicalFp206.p := by decide +kernel

theorem imaginary_square : imaginary * imaginary = -1 := by
  have cast := congrArg (fun value : Nat => (value : F)) imaginary_integer_equation
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self,
    mul_zero] at cast
  exact eq_neg_of_add_eq_zero_left cast

theorem coefficient_integer_equation :
    10241 * coefficientNat + 10240 = 3761 * CanonicalFp206.p := by decide +kernel

theorem coefficient_formula : coefficient = -(10240 : F) / 10241 := by
  have positive : (10241 : F) ≠ 0 := by
    intro zero
    have divides : CanonicalFp206.p ∣ 10241 :=
      (CharP.cast_eq_zero_iff F CanonicalFp206.p 10241).mp (by simpa only [Nat.cast_ofNat] using zero)
    exact Nat.not_le_of_gt (by decide : 10241 < CanonicalFp206.p)
      (Nat.le_of_dvd (by decide : 0 < 10241) divides)
  have cast := congrArg (fun value : Nat => (value : F)) coefficient_integer_equation
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self, mul_zero] at cast
  apply (eq_div_iff positive).mpr
  simpa only [coefficient, mul_comm] using eq_neg_of_add_eq_zero_left cast

theorem half_twice : half * 2 = CanonicalFp206.p - 1 := by decide +kernel

theorem euler_checked :
    ModularPower.power CanonicalFp206.p coefficientNat half = CanonicalFp206.p - 1 := by decide +kernel

theorem euler : coefficient ^ half = -1 := by
  have evaluated := ModularPower.power_sound CanonicalFp206.p coefficientNat half
  rw [euler_checked] at evaluated
  have count : CanonicalFp206.p - 1 + 1 = CanonicalFp206.p := by decide
  have cast := congrArg (fun value : Nat => (value : F)) count
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at cast
  exact evaluated.symm.trans (eq_neg_of_add_eq_zero_left cast)

theorem coefficient_no_unit_square : Group.NoUnitSquare coefficient := by
  exact Euler.nonsquare_of_euler (by simp [F, ConcreteRepresentation274.F, CanonicalFp206.Fp, ZMod.card]) half_twice two_ne_zero coefficient euler

theorem captured_d : (CapturedFirstSubgroup81.d:F)=coefficient := by
 simp only [CapturedFirstSubgroup81.d,coefficient,coefficientNat,Int.cast_ofNat,Nat.cast_ofNat]
theorem captured_no_unit_square : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F) := by
 rw [captured_d]
 exact coefficient_no_unit_square
end ShielddSecurity.ConcreteFieldParameters280

set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.Euler.finite_field_power
#print axioms ShielddSecurity.ConcreteFieldParameters280.Euler.finite_field_power
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.Euler.nonsquare_of_euler
#print axioms ShielddSecurity.ConcreteFieldParameters280.Euler.nonsquare_of_euler
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.F
#print axioms ShielddSecurity.ConcreteFieldParameters280.F
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.modulusNonzero
#print axioms ShielddSecurity.ConcreteFieldParameters280.modulusNonzero
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.coefficientNat
#print axioms ShielddSecurity.ConcreteFieldParameters280.coefficientNat
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.coefficient
#print axioms ShielddSecurity.ConcreteFieldParameters280.coefficient
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.imaginaryNat
#print axioms ShielddSecurity.ConcreteFieldParameters280.imaginaryNat
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.imaginary
#print axioms ShielddSecurity.ConcreteFieldParameters280.imaginary
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.half
#print axioms ShielddSecurity.ConcreteFieldParameters280.half
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.two_ne_zero
#print axioms ShielddSecurity.ConcreteFieldParameters280.two_ne_zero
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.imaginary_integer_equation
#print axioms ShielddSecurity.ConcreteFieldParameters280.imaginary_integer_equation
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.imaginary_square
#print axioms ShielddSecurity.ConcreteFieldParameters280.imaginary_square
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.coefficient_integer_equation
#print axioms ShielddSecurity.ConcreteFieldParameters280.coefficient_integer_equation
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.coefficient_formula
#print axioms ShielddSecurity.ConcreteFieldParameters280.coefficient_formula
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.half_twice
#print axioms ShielddSecurity.ConcreteFieldParameters280.half_twice
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.euler_checked
#print axioms ShielddSecurity.ConcreteFieldParameters280.euler_checked
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.euler
#print axioms ShielddSecurity.ConcreteFieldParameters280.euler
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.coefficient_no_unit_square
#print axioms ShielddSecurity.ConcreteFieldParameters280.coefficient_no_unit_square
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.captured_d
#print axioms ShielddSecurity.ConcreteFieldParameters280.captured_d
set_option pp.all true in
#check @ShielddSecurity.ConcreteFieldParameters280.captured_no_unit_square
#print axioms ShielddSecurity.ConcreteFieldParameters280.captured_no_unit_square
