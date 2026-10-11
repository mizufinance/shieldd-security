import ShielddSecurity.NextComparison115Rename
import ShielddSecurity.CapturedValueComparison104C03
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.NextComparison115Rows03
open Compiler CompilerAssertionBlock51
noncomputable def actualRows : List Row := CompilerColumnRenaming05.rows NextComparison115.rename CapturedValueComparison104C03.actualRows
theorem rows_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 10716 64 actualRows=true := by decide +kernel
theorem selected_satisfies {F : Type} [Field F] (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Satisfies rho actualRows :=
  CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 10716 64 actualRows rows_checked (by decide) rho arithmetic
end ShielddSecurity.NextComparison115Rows03

set_option pp.all true in
#check @ShielddSecurity.NextComparison115Rows03.actualRows
#print axioms ShielddSecurity.NextComparison115Rows03.actualRows
set_option pp.all true in
#check @ShielddSecurity.NextComparison115Rows03.rows_checked
#print axioms ShielddSecurity.NextComparison115Rows03.rows_checked
set_option pp.all true in
#check @ShielddSecurity.NextComparison115Rows03.selected_satisfies
#print axioms ShielddSecurity.NextComparison115Rows03.selected_satisfies
