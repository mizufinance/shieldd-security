import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedValueComparison105
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.NextComparison115
def rename (column : Nat) : Nat :=
  if 216≤column ∧ column<471 then column+510
  else if 32246≤column ∧ column<32754 then column+1016 else column
theorem copy_fixed : rename CompilerArithmeticTransport41.copy=CompilerArithmeticTransport41.copy := by decide
end ShielddSecurity.NextComparison115

set_option pp.all true in
#check @ShielddSecurity.NextComparison115.rename
#print axioms ShielddSecurity.NextComparison115.rename
set_option pp.all true in
#check @ShielddSecurity.NextComparison115.copy_fixed
#print axioms ShielddSecurity.NextComparison115.copy_fixed
