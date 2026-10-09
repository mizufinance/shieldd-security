import ShielddSecurity.Group
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 300000

namespace ShielddSecurity.Jubjub

variable {F : Type} [Field F]

/-- Each generated step checks only one bounded integer multiplication and
reduction. Kernel evaluation never expands the full 254-bit exponent. -/
theorem power_square {p : Nat} [CharP F p] (base residue next : Int) (exponent : Nat)
    (previous : (base : F) ^ exponent = (residue : F))
    (checked : (residue * residue) % (p : Int) = next) :
    (base : F) ^ (exponent * 2) = (next : F) := by
  have reduced := Compiler.coefficient_mod (F := F) (p := p) (residue * residue)
  rw [checked] at reduced
  calc
    _ = (residue : F) * (residue : F) := by rw [pow_mul, previous]; ring
    _ = ((residue * residue : Int) : F) := by simp only [Int.cast_mul]
    _ = (next : F) := reduced.symm

theorem power_square_multiply {p : Nat} [CharP F p]
    (base residue next : Int) (exponent : Nat)
    (previous : (base : F) ^ exponent = (residue : F))
    (checked : (residue * residue * base) % (p : Int) = next) :
    (base : F) ^ (exponent * 2 + 1) = (next : F) := by
  have reduced := Compiler.coefficient_mod (F := F) (p := p) (residue * residue * base)
  rw [checked] at reduced
  calc
    _ = (residue : F) * (residue : F) * (base : F) := by
      rw [pow_add, pow_mul, previous, pow_one]; ring
    _ = ((residue * residue * base : Int) : F) := by simp only [Int.cast_mul]
    _ = (next : F) := reduced.symm

theorem product_certificate {p : Nat} [CharP F p] (left right result : Int)
    (checked : (left * right) % (p : Int) = result) :
    (left : F) * (right : F) = (result : F) := by
  have reduced := Compiler.coefficient_mod (F := F) (p := p) (left * right)
  rw [checked, Int.cast_mul] at reduced
  exact reduced.symm

/-- Cardinality is essential: characteristic p alone also admits extension
fields, where the concrete Jubjub d can become a square. -/
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

#print axioms power_square
#print axioms power_square_multiply
#print axioms product_certificate
#print axioms finite_field_power
#print axioms nonsquare_of_euler

end ShielddSecurity.Jubjub
