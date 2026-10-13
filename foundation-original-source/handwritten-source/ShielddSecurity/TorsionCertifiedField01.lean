import ShielddSecurity.FieldPrimeNode38
import ShielddSecurity.TorsionPrimeNonsquare01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TorsionCertifiedField01
open TorsionEulerInteger49

theorem modulus_prime : Nat.Prime modulus := FieldPrimeNode38.prime
instance primeFact : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

abbrev F := ZMod modulus
def A : F := 40962
def B : F := -40964

theorem B_nonzero : B ≠ 0 := by
  change -(40964 : F) ≠ 0
  apply neg_ne_zero.mpr
  intro zero
  have divides : modulus ∣ 40964 :=
    (CharP.cast_eq_zero_iff F modulus 40964).mp
      (by simpa only [Nat.cast_ofNat] using zero)
  exact Nat.not_le_of_gt (by decide +kernel : 40964 < modulus)
    (Nat.le_of_dvd (by decide : 0 < 40964) divides)

theorem discriminant_equation : A * A - 4 = (quadraticDiscriminant : F) := by
  have count : quadraticDiscriminant + 4 = 40962 * 40962 := by decide +kernel
  have cast := congrArg (fun value : Nat => (value : F)) count
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at cast
  exact (eq_sub_of_add_eq cast).symm

theorem first_nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare (firstX : F) :=
  TorsionPrimeNonsquare01.first_nonsquare

theorem second_nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare (secondX : F) :=
  TorsionPrimeNonsquare01.second_nonsquare

theorem discriminant_nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare (A * A - 4) := by
  rw [discriminant_equation]
  exact TorsionPrimeNonsquare01.discriminant_nonsquare

theorem scaled_discriminant_nonsquare :
    WeierstrassTwoTorsionAlgebra01.NoSquare
      ((A * B) * (A * B) - 4 * (B * B)) :=
  WeierstrassTwoTorsionAlgebra01.scaled_discriminant_nonsquare A B B_nonzero
    discriminant_nonsquare

/-- The actual short Weierstrass equation has only X=0 on Y=0.
Linking Y=0 to two-torsion of its Point group is a separate obligation. -/
theorem zero_y_forces_zero_x (x y : F)
    (equation : y * y = x * x * x + (A * B) * x * x + (B * B) * x)
    (zeroY : y = 0) : x = 0 :=
  WeierstrassTwoTorsionAlgebra01.zero_y_forces_zero_x (A * B) (B * B) x y
    equation zeroY scaled_discriminant_nonsquare

end ShielddSecurity.TorsionCertifiedField01

set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.modulus_prime
#print axioms ShielddSecurity.TorsionCertifiedField01.modulus_prime
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.primeFact
#print axioms ShielddSecurity.TorsionCertifiedField01.primeFact
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.F
#print axioms ShielddSecurity.TorsionCertifiedField01.F
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.A
#print axioms ShielddSecurity.TorsionCertifiedField01.A
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.B
#print axioms ShielddSecurity.TorsionCertifiedField01.B
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.B_nonzero
#print axioms ShielddSecurity.TorsionCertifiedField01.B_nonzero
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.discriminant_equation
#print axioms ShielddSecurity.TorsionCertifiedField01.discriminant_equation
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.first_nonsquare
#print axioms ShielddSecurity.TorsionCertifiedField01.first_nonsquare
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.second_nonsquare
#print axioms ShielddSecurity.TorsionCertifiedField01.second_nonsquare
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.discriminant_nonsquare
#print axioms ShielddSecurity.TorsionCertifiedField01.discriminant_nonsquare
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.scaled_discriminant_nonsquare
#print axioms ShielddSecurity.TorsionCertifiedField01.scaled_discriminant_nonsquare
set_option pp.all true in
#check @ShielddSecurity.TorsionCertifiedField01.zero_y_forces_zero_x
#print axioms ShielddSecurity.TorsionCertifiedField01.zero_y_forces_zero_x
