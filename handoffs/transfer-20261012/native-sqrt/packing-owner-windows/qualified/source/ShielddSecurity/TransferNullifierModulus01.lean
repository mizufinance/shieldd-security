import Init.Data.Nat.Basic
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBoundedNativeCodec01

def nullifierModulus : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513

set_option pp.all true in
#check @nullifierModulus
#print axioms nullifierModulus
end ShielddSecurity.TransferBoundedNativeCodec01
