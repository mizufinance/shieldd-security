import ShielddSecurity.ConcreteAuthorizationCrypto430
import ShielddSecurity.CompilerColumnRenaming05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableDoubleTemplate431
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]

/-- Ports: 0=one, 1/2=input, 3/4=output, 5..11=arithmetic intermediates. -/
def arithmeticRows : List Row :=
 [⟨[(1,1)],[(5,1)]⟩,⟨[(2,1)],[(6,1)]⟩,⟨[(1,1),(2,1)],[(7,1)]⟩,
  ⟨[(3,1),(5,1),(6,-1)],[(9,1)]⟩,⟨[(3,1),(5,-1),(6,1)],[(8,4),(9,1)]⟩,
  ⟨[(0,-2),(4,1),(5,-1),(6,1)],[(11,1)]⟩,
  ⟨[(0,2),(4,1),(5,1),(6,-1)],[(10,4),(11,1)]⟩]

def assertionRows : List Row :=
 [⟨subtract [(8,1)] [(7,1),(5,-1),(6,-1)],[]⟩,
  ⟨subtract [(10,1)] [(5,1),(6,1)],[]⟩]

theorem values (rho : Nat → F) (one : rho 0=1) (arithmetic : Satisfies rho arithmeticRows) :
    rho 5=rho 1*rho 1 ∧ rho 6=rho 2*rho 2 ∧
    rho 7=(rho 1+rho 2)*(rho 1+rho 2) ∧
    rho 8=rho 3*(rho 6-rho 5) ∧ rho 10=rho 4*(2-(rho 6-rho 5)) := by
  have xx := checked_square_sound rho arithmeticRows [(1,1)] [(5,1)] arithmetic (by decide +kernel)
  have yy := checked_square_sound rho arithmeticRows [(2,1)] [(6,1)] arithmetic (by decide +kernel)
  have sum := checked_square_sound rho arithmeticRows [(1,1),(2,1)] [(7,1)] arithmetic (by decide +kernel)
  have px := checked_product_sound rho arithmeticRows [(3,1)] [(6,1),(5,-1)] [(8,1)] [(9,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have py := checked_product_sound rho arithmeticRows [(4,1)] [(0,2),(5,1),(6,-1)] [(10,1)] [(11,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  simp only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,neg_mul,add_zero,one, mul_one] at xx yy sum px py
  exact ⟨xx,yy,sum,by simpa only [sub_eq_add_neg,add_comm] using px,by simpa only [sub_eq_add_neg,neg_add_rev,neg_neg,add_assoc] using py⟩

theorem equality_row (rho : Nat → F) (left right : Linear) :
    Square (eval rho (subtract left right)) 0 ↔ eval rho left=eval rho right := by
  rw [eval_subtract]
  change Square (eval rho left-eval rho right) 0 ↔ _
  constructor
  · intro h
    exact sub_eq_zero.mp (square_zero _ h)
  · intro h
    rw [h,sub_self]
    exact zero_mul 0

theorem assertions_iff (rho : Nat → F) : Satisfies rho assertionRows ↔
    rho 8=rho 7-rho 5-rho 6 ∧ rho 10=rho 5+rho 6 := by
  simp only [Satisfies,assertionRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,equality_row,eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,
    sub_eq_add_neg,add_assoc]

theorem double_iff (rho : Nat → F) (one : rho 0=1) (arithmetic : Satisfies rho arithmeticRows) :
    Satisfies rho assertionRows ↔ TransferOwnership.DoubleEquations ⟨rho 1,rho 2⟩ ⟨rho 3,rho 4⟩ := by
  obtain ⟨xx,yy,sum,px,py⟩ := values rho one arithmetic
  rw [assertions_iff,px,py,xx,yy,sum]
  simp only [TransferOwnership.DoubleEquations,add_comm]
end ShielddSecurity.VariableDoubleTemplate431

set_option pp.all true in
#check @ShielddSecurity.VariableDoubleTemplate431.arithmeticRows
#print axioms ShielddSecurity.VariableDoubleTemplate431.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.VariableDoubleTemplate431.assertionRows
#print axioms ShielddSecurity.VariableDoubleTemplate431.assertionRows

set_option pp.all true in
#check @ShielddSecurity.VariableDoubleTemplate431.values
#print axioms ShielddSecurity.VariableDoubleTemplate431.values

set_option pp.all true in
#check @ShielddSecurity.VariableDoubleTemplate431.equality_row
#print axioms ShielddSecurity.VariableDoubleTemplate431.equality_row

set_option pp.all true in
#check @ShielddSecurity.VariableDoubleTemplate431.assertions_iff
#print axioms ShielddSecurity.VariableDoubleTemplate431.assertions_iff

set_option pp.all true in
#check @ShielddSecurity.VariableDoubleTemplate431.double_iff
#print axioms ShielddSecurity.VariableDoubleTemplate431.double_iff
