-- GENERATED from extraction.json. Do not hand edit.
import ShielddSecurity.MapArithmeticCapture705B00
import ShielddSecurity.MapArithmeticCapture705B01
import ShielddSecurity.MapArithmeticCapture705B02
import ShielddSecurity.MapArithmeticCapture705B03
import ShielddSecurity.MapArithmeticCapture705B04
import ShielddSecurity.MapArithmeticCapture705B05
import ShielddSecurity.MapArithmeticCapture705B06
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapArithmeticCapture705
open MapArithmeticAdapter704 Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def entries : List Entry := MapArithmeticCapture705B00.entries++MapArithmeticCapture705B01.entries++MapArithmeticCapture705B02.entries++MapArithmeticCapture705B03.entries++MapArithmeticCapture705B04.entries++MapArithmeticCapture705B05.entries++MapArithmeticCapture705B06.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,MapArithmeticCapture705B00.checked,MapArithmeticCapture705B01.checked,MapArithmeticCapture705B02.checked,MapArithmeticCapture705B03.checked,MapArithmeticCapture705B04.checked,MapArithmeticCapture705B05.checked,MapArithmeticCapture705B06.checked,Bool.true_and]
theorem equations {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    ∀ e∈entries, eval rho e.output=if e.square then eval rho e.left*eval rho e.left else eval rho e.left*eval rho e.right := by
  intro e member
  exact equation e (List.all_eq_true.mp checked e member) rho arithmetic
end ShielddSecurity.MapArithmeticCapture705

set_option pp.all true in
#check @ShielddSecurity.MapArithmeticCapture705.checked
#print axioms ShielddSecurity.MapArithmeticCapture705.checked

set_option pp.all true in
#check @ShielddSecurity.MapArithmeticCapture705.equations
#print axioms ShielddSecurity.MapArithmeticCapture705.equations
