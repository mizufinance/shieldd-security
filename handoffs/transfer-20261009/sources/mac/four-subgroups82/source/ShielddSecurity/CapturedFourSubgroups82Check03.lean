import ShielddSecurity.CapturedFourSubgroups82Core
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CapturedFourSubgroups82Check03
theorem checked : CapturedFourSubgroups82.rowCheck ⟨2,by decide⟩=true := by decide +kernel
end ShielddSecurity.CapturedFourSubgroups82Check03

set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82Check03.checked
#print axioms ShielddSecurity.CapturedFourSubgroups82Check03.checked
