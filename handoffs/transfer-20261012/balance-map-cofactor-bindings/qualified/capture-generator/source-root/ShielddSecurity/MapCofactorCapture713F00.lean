-- GENERATED from families.json. Do not hand edit.
import ShielddSecurity.MapCofactorAdapter712
import Mathlib.Tactic.IntervalCases
import ShielddSecurity.MapArithmeticCapture705B02
import ShielddSecurity.MapArithmeticCapture705B03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapCofactorCapture713F00
open MapCofactorAdapter712 CompilerAssertionBlock51 ConcreteJubjubField01
noncomputable def layout : Layout := ⟨[(190177,1)],[(21193,1),(190181,1)],21195,190183⟩
theorem checked0 : check layout 0 MapArithmeticCapture705B02.entry2=true := by decide +kernel
theorem checked1 : check layout 1 MapArithmeticCapture705B02.entry3=true := by decide +kernel
theorem checked2 : check layout 2 MapArithmeticCapture705B02.entry4=true := by decide +kernel
theorem checked3 : check layout 3 MapArithmeticCapture705B02.entry5=true := by decide +kernel
theorem checked4 : check layout 4 MapArithmeticCapture705B02.entry6=true := by decide +kernel
theorem checked5 : check layout 5 MapArithmeticCapture705B03.entry0=true := by decide +kernel
theorem checked6 : check layout 6 MapArithmeticCapture705B03.entry1=true := by decide +kernel
theorem checked7 : check layout 7 MapArithmeticCapture705B03.entry2=true := by decide +kernel
theorem checked8 : check layout 8 MapArithmeticCapture705B03.entry3=true := by decide +kernel
theorem checked9 : check layout 9 MapArithmeticCapture705B03.entry4=true := by decide +kernel
theorem checked10 : check layout 10 MapArithmeticCapture705B03.entry5=true := by decide +kernel
theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    ∀ index<11, Equation rho layout index := by
  intro index bound
  interval_cases index
  · exact equation layout 0 MapArithmeticCapture705B02.entry2 checked0 MapArithmeticCapture705B02.checked2 rho arithmetic
  · exact equation layout 1 MapArithmeticCapture705B02.entry3 checked1 MapArithmeticCapture705B02.checked3 rho arithmetic
  · exact equation layout 2 MapArithmeticCapture705B02.entry4 checked2 MapArithmeticCapture705B02.checked4 rho arithmetic
  · exact equation layout 3 MapArithmeticCapture705B02.entry5 checked3 MapArithmeticCapture705B02.checked5 rho arithmetic
  · exact equation layout 4 MapArithmeticCapture705B02.entry6 checked4 MapArithmeticCapture705B02.checked6 rho arithmetic
  · exact equation layout 5 MapArithmeticCapture705B03.entry0 checked5 MapArithmeticCapture705B03.checked0 rho arithmetic
  · exact equation layout 6 MapArithmeticCapture705B03.entry1 checked6 MapArithmeticCapture705B03.checked1 rho arithmetic
  · exact equation layout 7 MapArithmeticCapture705B03.entry2 checked7 MapArithmeticCapture705B03.checked2 rho arithmetic
  · exact equation layout 8 MapArithmeticCapture705B03.entry3 checked8 MapArithmeticCapture705B03.checked3 rho arithmetic
  · exact equation layout 9 MapArithmeticCapture705B03.entry4 checked9 MapArithmeticCapture705B03.checked4 rho arithmetic
  · exact equation layout 10 MapArithmeticCapture705B03.entry5 checked10 MapArithmeticCapture705B03.checked5 rho arithmetic
end ShielddSecurity.MapCofactorCapture713F00

set_option pp.all true in
#check @ShielddSecurity.MapCofactorCapture713F00.equations
#print axioms ShielddSecurity.MapCofactorCapture713F00.equations
