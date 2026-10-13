import ShielddSecurity.CapturedRkInverse508
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RkInverseRows513
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] CapturedFullRelation58.rowAt

theorem rows (rho : Nat → F) (value : F) (zero : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (x : rho 4272=value) (inverse : rho 4279=value⁻¹) (nonzero : value≠0) :
    CapturedRkInverse508.Rows rho := by
  apply CapturedRkInverse508.complete rho zero (copied.trans zero.symm)
  intro index bound
  have same : index=0 := by omega
  subst index
  have product := CapturedRkInverse508.products rho arithmetic 0 (by decide)
  simp only [CapturedRkInverse508.operandTerms,CapturedRkInverse508.hintColumn,Nat.add_zero,
    eval,Int.cast_one,one_mul,add_zero] at product
  rw [x,inverse] at product
  exact product.trans (mul_inv_cancel₀ nonzero)
end ShielddSecurity.RkInverseRows513
set_option pp.all true in
#check @ShielddSecurity.RkInverseRows513.rows
#print axioms ShielddSecurity.RkInverseRows513.rows
