import ShielddSecurity.NatModularPower01
import ShielddSecurity.CurveCardinalityWindow01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TorsionEulerInteger49

def modulus : Nat := CurveCardinalityWindow01.fieldModulus

def half : Nat :=
  26217937587563095239723870254092982918845276250263818911301829349969290592256

def firstX : Nat :=
  40969977092314373855427314892644412412056592297350547336836035604665542479344

def secondX : Nat :=
  37748634194707046026986136096002964518686894419990801728560193225894679879758

def quadraticDiscriminant : Nat := 40962 * 40962 - 4

theorem half_twice : half * 2 = modulus - 1 := by decide +kernel

theorem first_bound : firstX < modulus := by decide +kernel

theorem second_bound : secondX < modulus := by decide +kernel

/-- Closed integer binary-exponentiation certificates. These do not establish
point order, an exhaustive torsion list, native coordinates, or curve cardinality.
Their field interpretation requires a separately proved field soundness theorem and the actual
certified field/cardinality interface. -/
theorem first_euler_checked :
    NatModularPower01.power modulus firstX half = modulus - 1 := by decide +kernel

theorem second_euler_checked :
    NatModularPower01.power modulus secondX half = modulus - 1 := by decide +kernel

theorem discriminant_euler_checked :
    NatModularPower01.power modulus quadraticDiscriminant half = modulus - 1 := by decide +kernel

end ShielddSecurity.TorsionEulerInteger49

set_option pp.all true in
#check @ShielddSecurity.TorsionEulerInteger49.half_twice
#print axioms ShielddSecurity.TorsionEulerInteger49.half_twice
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerInteger49.first_bound
#print axioms ShielddSecurity.TorsionEulerInteger49.first_bound
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerInteger49.second_bound
#print axioms ShielddSecurity.TorsionEulerInteger49.second_bound
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerInteger49.first_euler_checked
#print axioms ShielddSecurity.TorsionEulerInteger49.first_euler_checked
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerInteger49.second_euler_checked
#print axioms ShielddSecurity.TorsionEulerInteger49.second_euler_checked
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerInteger49.discriminant_euler_checked
#print axioms ShielddSecurity.TorsionEulerInteger49.discriminant_euler_checked
