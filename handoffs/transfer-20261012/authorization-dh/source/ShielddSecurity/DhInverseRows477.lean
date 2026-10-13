import ShielddSecurity.CapturedDhInverse472
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DhInverseRows477
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] CapturedFullRelation58.rowAt

theorem rows (rho : Nat → F) (value : F) (zero : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (x : rho 3763=value) (inverse : rho 3765=value⁻¹) (nonzero : value≠0) :
    CapturedDhInverse472.Rows rho := by
  apply CapturedDhInverse472.complete rho zero (copied.trans zero.symm)
  intro index bound
  have same : index=0 := by omega
  subst index
  have product := CapturedDhInverse472.products rho arithmetic 0 (by decide)
  simp only [CapturedDhInverse472.operandTerms,CapturedDhInverse472.hintColumn,Nat.add_zero,
    eval,Int.cast_one,one_mul,add_zero] at product
  rw [x,inverse] at product
  exact product.trans (mul_inv_cancel₀ nonzero)
end ShielddSecurity.DhInverseRows477
set_option pp.all true in
#check @ShielddSecurity.DhInverseRows477.rows
#print axioms ShielddSecurity.DhInverseRows477.rows
