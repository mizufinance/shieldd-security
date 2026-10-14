-- GENERATED from families.json. Do not hand edit.
import ShielddSecurity.MapCofactorAdapter712
import Mathlib.Tactic.IntervalCases
import ShielddSecurity.MapArithmeticCapture705B05
import ShielddSecurity.MapArithmeticCapture705B06
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapCofactorCapture713F02
open MapCofactorAdapter712 CompilerAssertionBlock51 ConcreteJubjubField01
noncomputable def layout : Layout := ⟨[(190217,1)],[(190221,1)],21197,190223⟩
theorem checked0 : check layout 0 MapArithmeticCapture705B05.entry3=true := by decide +kernel
theorem checked1 : check layout 1 MapArithmeticCapture705B05.entry4=true := by decide +kernel
theorem checked2 : check layout 2 MapArithmeticCapture705B05.entry5=true := by decide +kernel
theorem checked3 : check layout 3 MapArithmeticCapture705B05.entry6=true := by decide +kernel
theorem checked4 : check layout 4 MapArithmeticCapture705B06.entry0=true := by decide +kernel
theorem checked5 : check layout 5 MapArithmeticCapture705B06.entry1=true := by decide +kernel
theorem checked6 : check layout 6 MapArithmeticCapture705B06.entry2=true := by decide +kernel
theorem checked7 : check layout 7 MapArithmeticCapture705B06.entry3=true := by decide +kernel
theorem checked8 : check layout 8 MapArithmeticCapture705B06.entry4=true := by decide +kernel
theorem checked9 : check layout 9 MapArithmeticCapture705B06.entry5=true := by decide +kernel
theorem checked10 : check layout 10 MapArithmeticCapture705B06.entry6=true := by decide +kernel
theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    ∀ index<11, Equation rho layout index := by
  intro index bound
  interval_cases index
  · exact equation layout 0 MapArithmeticCapture705B05.entry3 checked0 MapArithmeticCapture705B05.checked3 rho arithmetic
  · exact equation layout 1 MapArithmeticCapture705B05.entry4 checked1 MapArithmeticCapture705B05.checked4 rho arithmetic
  · exact equation layout 2 MapArithmeticCapture705B05.entry5 checked2 MapArithmeticCapture705B05.checked5 rho arithmetic
  · exact equation layout 3 MapArithmeticCapture705B05.entry6 checked3 MapArithmeticCapture705B05.checked6 rho arithmetic
  · exact equation layout 4 MapArithmeticCapture705B06.entry0 checked4 MapArithmeticCapture705B06.checked0 rho arithmetic
  · exact equation layout 5 MapArithmeticCapture705B06.entry1 checked5 MapArithmeticCapture705B06.checked1 rho arithmetic
  · exact equation layout 6 MapArithmeticCapture705B06.entry2 checked6 MapArithmeticCapture705B06.checked2 rho arithmetic
  · exact equation layout 7 MapArithmeticCapture705B06.entry3 checked7 MapArithmeticCapture705B06.checked3 rho arithmetic
  · exact equation layout 8 MapArithmeticCapture705B06.entry4 checked8 MapArithmeticCapture705B06.checked4 rho arithmetic
  · exact equation layout 9 MapArithmeticCapture705B06.entry5 checked9 MapArithmeticCapture705B06.checked5 rho arithmetic
  · exact equation layout 10 MapArithmeticCapture705B06.entry6 checked10 MapArithmeticCapture705B06.checked6 rho arithmetic
end ShielddSecurity.MapCofactorCapture713F02

set_option pp.all true in
#check @ShielddSecurity.MapCofactorCapture713F02.equations
#print axioms ShielddSecurity.MapCofactorCapture713F02.equations
