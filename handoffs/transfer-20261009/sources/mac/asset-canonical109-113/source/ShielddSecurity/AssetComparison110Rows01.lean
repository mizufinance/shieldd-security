import ShielddSecurity.AssetComparison110Rename
import ShielddSecurity.CapturedValueComparison104C01
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AssetComparison110Rows01
open Compiler CompilerAssertionBlock51
noncomputable def actualRows : List Row := CompilerColumnRenaming05.rows AssetComparison110.rename CapturedValueComparison104C01.actualRows
theorem rows_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 10080 64 actualRows=true := by decide +kernel
theorem selected_satisfies {F : Type} [Field F] (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Satisfies rho actualRows :=
  CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 10080 64 actualRows rows_checked (by decide) rho arithmetic
end ShielddSecurity.AssetComparison110Rows01

set_option pp.all true in
#check @ShielddSecurity.AssetComparison110Rows01.actualRows
#print axioms ShielddSecurity.AssetComparison110Rows01.actualRows
set_option pp.all true in
#check @ShielddSecurity.AssetComparison110Rows01.rows_checked
#print axioms ShielddSecurity.AssetComparison110Rows01.rows_checked
set_option pp.all true in
#check @ShielddSecurity.AssetComparison110Rows01.selected_satisfies
#print axioms ShielddSecurity.AssetComparison110Rows01.selected_satisfies
