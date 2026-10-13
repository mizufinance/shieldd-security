import ShielddSecurity.UserSubgroupCapture355B05Base
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserSubgroupCapture355B05Check3
open UserSubgroupCapture355B05
theorem checked : (List.range 16).all (fun offset => decide (CapturedFullArithmetic52.rowAt (19156+(48+offset))=arithmeticRows[48+offset]?)) = true := by decide +kernel
end ShielddSecurity.UserSubgroupCapture355B05Check3
set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355B05Check3.checked
#print axioms ShielddSecurity.UserSubgroupCapture355B05Check3.checked
