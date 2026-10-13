import ShielddSecurity.Rows
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.WeightedDelta335
variable {F : Type} [Field F]
theorem meaning (rho : Nat → F) (left right : List Nat) (a b : F)
    (leftMeaning : fieldBinary (left.map rho)=a) (rightMeaning : fieldBinary (right.map rho)=b) :
    eval rho (weighted right (-1)++weighted left 1)=a-b := by
  rw [eval_append,weighted_eval,weighted_eval,leftMeaning,rightMeaning]
  simp only [Int.cast_neg,Int.cast_one,neg_one_mul,one_mul]
  ring
end ShielddSecurity.WeightedDelta335
set_option pp.all true in
#check @ShielddSecurity.WeightedDelta335.meaning
#print axioms ShielddSecurity.WeightedDelta335.meaning
