-- GENERATED from families.json. Do not hand edit.
import ShielddSecurity.MapCofactorCapture713F00
import ShielddSecurity.MapCofactorCapture713F01
import ShielddSecurity.MapCofactorCapture713F02
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapCofactorCapture713
open MapCofactorAdapter712 CompilerAssertionBlock51 ConcreteJubjubField01
theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (∀ index<11, Equation rho MapCofactorCapture713F00.layout index) ∧
    (∀ index<11, Equation rho MapCofactorCapture713F01.layout index) ∧
    (∀ index<11, Equation rho MapCofactorCapture713F02.layout index) :=
  ⟨MapCofactorCapture713F00.equations rho arithmetic,MapCofactorCapture713F01.equations rho arithmetic,MapCofactorCapture713F02.equations rho arithmetic⟩
end ShielddSecurity.MapCofactorCapture713

set_option pp.all true in
#check @ShielddSecurity.MapCofactorCapture713.equations
#print axioms ShielddSecurity.MapCofactorCapture713.equations
