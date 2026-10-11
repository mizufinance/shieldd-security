import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedValueComparison105
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.AssetComparison110
def rename (column : Nat) : Nat :=
  if 216≤column ∧ column<471 then column+255
  else if 32246≤column ∧ column<32754 then column+508 else column
theorem copy_fixed : rename CompilerArithmeticTransport41.copy=CompilerArithmeticTransport41.copy := by decide
end ShielddSecurity.AssetComparison110
