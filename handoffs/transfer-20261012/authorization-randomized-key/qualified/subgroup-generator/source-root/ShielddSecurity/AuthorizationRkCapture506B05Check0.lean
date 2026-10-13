import ShielddSecurity.AuthorizationRkCapture506B05Base
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkCapture506B05Check0
open AuthorizationRkCapture506B05
theorem checked : (List.range 16).all (fun offset => decide (CapturedFullArithmetic52.rowAt (41724+(0+offset))=arithmeticRows[0+offset]?)) = true := by decide +kernel
end ShielddSecurity.AuthorizationRkCapture506B05Check0
set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkCapture506B05Check0.checked
#print axioms ShielddSecurity.AuthorizationRkCapture506B05Check0.checked
