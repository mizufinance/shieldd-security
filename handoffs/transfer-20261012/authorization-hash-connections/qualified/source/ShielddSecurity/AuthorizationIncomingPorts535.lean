import ShielddSecurity.AuthorizationHash530C55
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationIncomingPorts535
variable {F : Type} [Field F]
theorem inputs (rho : Nat → F) (nk ax ay : F)
    (key : rho 1993=nk) (x : rho 1980=ax) (y : rho 1981=ay) :
    AuthorizationHash530C55.values rho=[nk,ax,ay] := by
  simp only [AuthorizationHash530C55.values,AuthorizationHash530C55.inputs,
    List.map_cons,List.map_nil,eval,Int.cast_one,one_mul,add_zero,key,x,y]
end ShielddSecurity.AuthorizationIncomingPorts535
set_option pp.all true in
#check @ShielddSecurity.AuthorizationIncomingPorts535.inputs
#print axioms ShielddSecurity.AuthorizationIncomingPorts535.inputs
