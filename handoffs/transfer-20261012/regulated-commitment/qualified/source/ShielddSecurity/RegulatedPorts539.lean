import ShielddSecurity.RegulatedCapture538
import ShielddSecurity.AuthorizationRingProduct420A
import ShielddSecurity.AuthorizationHash530C56
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegulatedPorts539
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
theorem regulated_inputs (rho : Nat → F) (one : rho 0=1) (copied : rho copy=1)
    (flag : rho 10=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (dx dy ax ay tx ty asset rx ry : F)
    (hdx : rho 3763=dx) (hdy : rho 3764=dy)
    (hax : rho 1504=ax) (hay : rho 1505=ay)
    (htx : rho 1512=tx) (hty : rho 1513=ty)
    (ha : rho 6=asset) (hrx : rho 23=rx) (hry : rho 24=ry) :
    AuthorizationHash530C56.values rho=[dx,dy,ax,ay,tx,ty,asset,rx,ry] := by
  have x := AuthorizationRingProduct420A.ring_product rho arithmetic
  have y := RegulatedCapture538.ring_y rho arithmetic
  simp only [flag,copied,one_mul,mul_one] at x y
  simp only [AuthorizationHash530C56.values,AuthorizationHash530C56.inputs,List.map_cons,List.map_nil,
    eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,x,y,hdx,hdy,hax,hay,htx,hty,ha,hrx,hry,mul_one]
  congr 12 <;> ring
end ShielddSecurity.RegulatedPorts539
set_option pp.all true in
#check @ShielddSecurity.RegulatedPorts539.regulated_inputs
#print axioms ShielddSecurity.RegulatedPorts539.regulated_inputs
