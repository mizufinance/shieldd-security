import ShielddSecurity.AuthorizationSubgroupCapture409B05Base
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSubgroupCapture409B05Check0
open AuthorizationSubgroupCapture409B05
theorem checked : (List.range 16).all (fun offset => decide (CapturedFullArithmetic52.rowAt (26978+(0+offset))=arithmeticRows[0+offset]?)) = true := by decide +kernel
end ShielddSecurity.AuthorizationSubgroupCapture409B05Check0
set_option pp.all true in
#check @ShielddSecurity.AuthorizationSubgroupCapture409B05Check0.checked
#print axioms ShielddSecurity.AuthorizationSubgroupCapture409B05Check0.checked
