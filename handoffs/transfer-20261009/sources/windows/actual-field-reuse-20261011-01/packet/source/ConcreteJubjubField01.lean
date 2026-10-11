import ShielddSecurity.FieldPrimeNode38
import ShielddSecurity.Jubjub
import ShielddSecurity.GroupByteCodec

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteJubjubField01

theorem modulus_prime : Nat.Prime Scalar.modulus := FieldPrimeNode38.prime
instance primeFact : Fact (Nat.Prime Scalar.modulus) := ⟨modulus_prime⟩
instance modulusNonzero : NeZero Scalar.modulus := ⟨by decide⟩

abbrev F := ZMod Scalar.modulus

/-- A concrete mathematical prime-field codec. Its correspondence with the
native Scalar FFI encoder/reader remains a separate refinement obligation. -/
def canonical : TransferReduction.CanonicalField F where
  decode value := value.val
  bounded value := ZMod.val_lt value
  roundtrip value := ZMod.natCast_zmod_val value

def writer : GroupByteCodec.BEWrite canonical := GroupByteCodec.canonicalWrite canonical

def coefficientNat : Nat :=
  19257038036680949359750312669786877991949435402254120286184196891950884077233
def coefficient : F := (coefficientNat : F)
def imaginaryNat : Nat := 3465144826073652318776269530687742778270252468765361963008
def imaginary : F := (imaginaryNat : F)
def half : Nat := 26217937587563095239723870254092982918845276250263818911301829349969290592256

theorem two_ne_zero : (2 : F) ≠ 0 := by
  intro zero
  have divides : Scalar.modulus ∣ 2 :=
    (CharP.cast_eq_zero_iff F Scalar.modulus 2).mp (by simpa only [Nat.cast_ofNat] using zero)
  exact Nat.not_le_of_gt (by decide : 2 < Scalar.modulus)
    (Nat.le_of_dvd (by decide : 0 < 2) divides)

theorem imaginary_integer_equation :
    imaginaryNat * imaginaryNat + 1 =
      228988810152649578064853576960394133505 * Scalar.modulus := by decide +kernel

theorem imaginary_square : imaginary * imaginary = -1 := by
  have cast := congrArg (fun value : Nat => (value : F)) imaginary_integer_equation
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self,
    mul_zero] at cast
  exact eq_neg_of_add_eq_zero_left cast

theorem coefficient_integer_equation :
    10241 * coefficientNat + 10240 = 3761 * Scalar.modulus := by decide +kernel

theorem coefficient_formula : coefficient = -(10240 : F) / 10241 := by
  have positive : (10241 : F) ≠ 0 := by
    intro zero
    have divides : Scalar.modulus ∣ 10241 :=
      (CharP.cast_eq_zero_iff F Scalar.modulus 10241).mp (by simpa only [Nat.cast_ofNat] using zero)
    exact Nat.not_le_of_gt (by decide : 10241 < Scalar.modulus)
      (Nat.le_of_dvd (by decide : 0 < 10241) divides)
  have cast := congrArg (fun value : Nat => (value : F)) coefficient_integer_equation
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self, mul_zero] at cast
  apply (eq_div_iff positive).mpr
  simpa only [coefficient, mul_comm] using eq_neg_of_add_eq_zero_left cast

theorem half_twice : half * 2 = Scalar.modulus - 1 := by decide +kernel

theorem euler_checked :
    ModularPower.power Scalar.modulus coefficientNat half = Scalar.modulus - 1 := by decide +kernel

theorem euler : coefficient ^ half = -1 := by
  have evaluated := ModularPower.power_sound Scalar.modulus coefficientNat half
  rw [euler_checked] at evaluated
  have count : Scalar.modulus - 1 + 1 = Scalar.modulus := by decide
  have cast := congrArg (fun value : Nat => (value : F)) count
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at cast
  exact evaluated.symm.trans (eq_neg_of_add_eq_zero_left cast)

theorem coefficient_no_unit_square : Group.NoUnitSquare coefficient := by
  exact Jubjub.nonsquare_of_euler (by simp [F, ZMod.card]) half_twice two_ne_zero coefficient euler

end ShielddSecurity.ConcreteJubjubField01
