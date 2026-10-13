import ShielddSecurity.PointEqualityAdapter440
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TransmissionCapture468
open PointEqualityAdapter440
def entries : List Entry := [⟨[(3007,1)],[(3008,1)],[(1512,1)],[(1513,1)],3013,[⟨[(1512,52435875175126190479447740508185965837690552500527637822603658699938581184512),(3007,1)],[]⟩,⟨[(1513,52435875175126190479447740508185965837690552500527637822603658699938581184512),(3008,1)],[]⟩]⟩]
theorem checked : entries.all check=true := by decide +kernel
end ShielddSecurity.TransmissionCapture468

set_option pp.all true in
#check @ShielddSecurity.TransmissionCapture468.entries
#print axioms ShielddSecurity.TransmissionCapture468.entries

set_option pp.all true in
#check @ShielddSecurity.TransmissionCapture468.checked
#print axioms ShielddSecurity.TransmissionCapture468.checked
