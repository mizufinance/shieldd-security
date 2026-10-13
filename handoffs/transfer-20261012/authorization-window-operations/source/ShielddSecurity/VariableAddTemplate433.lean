import ShielddSecurity.VariablePortSubstitution432
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableAddTemplate433
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]

def coefficient : Int := CapturedFirstSubgroup81.d
/-- Ports: 0=one, 1/2=left, 3/4=right, 5/6=output; 7..18 are arithmetic intermediates. -/
def arithmeticRows : List Row :=
 [⟨[(1,1),(3,-1)],[(8,1)]⟩,⟨[(1,1),(3,1)],[(7,4),(8,1)]⟩,
  ⟨[(2,1),(4,-1)],[(10,1)]⟩,⟨[(2,1),(4,1)],[(9,4),(10,1)]⟩,
  ⟨[(1,1),(2,1),(3,-1),(4,-1)],[(12,1)]⟩,
  ⟨[(1,1),(2,1),(3,1),(4,1)],[(11,4),(12,1)]⟩,
  ⟨[(7,1),(9,-1)],[(14,1)]⟩,⟨[(7,1),(9,1)],[(13,4),(14,1)]⟩,
  ⟨[(0,-1),(5,1),(13,-coefficient)],[(16,1)]⟩,
  ⟨[(0,1),(5,1),(13,coefficient)],[(15,4),(16,1)]⟩,
  ⟨[(0,-1),(6,1),(13,coefficient)],[(18,1)]⟩,
  ⟨[(0,1),(6,1),(13,-coefficient)],[(17,4),(18,1)]⟩]
def assertionRows : List Row :=
 [⟨subtract [(15,1)] [(11,1),(7,-1),(9,-1)],[]⟩,
  ⟨subtract [(17,1)] [(7,1),(9,1)],[]⟩]

theorem values (rho : Nat → F) (one : rho 0=1) (arithmetic : Satisfies rho arithmeticRows) :
    rho 7=rho 1*rho 3 ∧ rho 9=rho 2*rho 4 ∧
    rho 11=(rho 1+rho 2)*(rho 3+rho 4) ∧ rho 13=rho 7*rho 9 ∧
    rho 15=rho 5*(1+(coefficient:F)*rho 13) ∧
    rho 17=rho 6*(1-(coefficient:F)*rho 13) := by
  have xx := checked_product_sound rho arithmeticRows [(1,1)] [(3,1)] [(7,1)] [(8,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have yy := checked_product_sound rho arithmeticRows [(2,1)] [(4,1)] [(9,1)] [(10,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have sum := checked_product_sound rho arithmeticRows [(1,1),(2,1)] [(3,1),(4,1)] [(11,1)] [(12,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have delta := checked_product_sound rho arithmeticRows [(7,1)] [(9,1)] [(13,1)] [(14,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have px := checked_product_sound rho arithmeticRows [(5,1)] [(0,1),(13,coefficient)] [(15,1)] [(16,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have py := checked_product_sound rho arithmeticRows [(6,1)] [(0,1),(13,-coefficient)] [(17,1)] [(18,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one] at xx yy sum delta px py
  exact ⟨xx,yy,sum,delta,px,by simpa only [sub_eq_add_neg] using py⟩

theorem assertions_iff (rho : Nat → F) : Satisfies rho assertionRows ↔
    rho 15=rho 11-rho 7-rho 9 ∧ rho 17=rho 7+rho 9 := by
  simp only [Satisfies,assertionRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,VariableDoubleTemplate431.equality_row,eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,
    sub_eq_add_neg,add_assoc]

theorem add_iff (rho : Nat → F) (one : rho 0=1) (arithmetic : Satisfies rho arithmeticRows) :
    Satisfies rho assertionRows ↔
      TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F) ⟨rho 1,rho 2⟩ ⟨rho 3,rho 4⟩ ⟨rho 5,rho 6⟩ := by
  obtain ⟨xx,yy,sum,delta,px,py⟩ := values rho one arithmetic
  rw [assertions_iff,px,py,delta,xx,yy,sum]
  simp only [TransferOwnership.AddEquations,Group.delta,coefficient,mul_assoc,mul_comm,mul_left_comm,add_comm]
end ShielddSecurity.VariableAddTemplate433

set_option pp.all true in
#check @ShielddSecurity.VariableAddTemplate433.coefficient
#print axioms ShielddSecurity.VariableAddTemplate433.coefficient

set_option pp.all true in
#check @ShielddSecurity.VariableAddTemplate433.arithmeticRows
#print axioms ShielddSecurity.VariableAddTemplate433.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.VariableAddTemplate433.assertionRows
#print axioms ShielddSecurity.VariableAddTemplate433.assertionRows

set_option pp.all true in
#check @ShielddSecurity.VariableAddTemplate433.values
#print axioms ShielddSecurity.VariableAddTemplate433.values

set_option pp.all true in
#check @ShielddSecurity.VariableAddTemplate433.assertions_iff
#print axioms ShielddSecurity.VariableAddTemplate433.assertions_iff

set_option pp.all true in
#check @ShielddSecurity.VariableAddTemplate433.add_iff
#print axioms ShielddSecurity.VariableAddTemplate433.add_iff
