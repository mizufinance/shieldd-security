import ShielddSecurity.TransferLongRecipeData01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferLongRecipeControls01
open Compiler CompilerIndexed01 TransferLongRecipeData01
-- Reuse the production consumer checker and exact certified graph/record table.
def changedCoefficient : Row :=
  ⟨match originalRow.a with | [] => [] | (column,coefficient)::tail => (column,coefficient+1)::tail, originalRow.b⟩
theorem coefficient_changed : changedCoefficient.a.head?=some (216,2) := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeControls01.coefficient_changed
#print axioms ShielddSecurity.TransferLongRecipeControls01.coefficient_changed
theorem coefficient_rejected : consumerCheck leftPort rightPort #[changedCoefficient]=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeControls01.coefficient_rejected
#print axioms ShielddSecurity.TransferLongRecipeControls01.coefficient_rejected
-- Local0 is the existing source input213, a non-equivalent earlier consumer port.
def earlierPort : Fin records.size := ⟨0,by change 0<1036;decide⟩
theorem dependency_rejected : consumerCheck earlierPort rightPort originalRows=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeControls01.dependency_rejected
#print axioms ShielddSecurity.TransferLongRecipeControls01.dependency_rejected
end ShielddSecurity.TransferLongRecipeControls01
