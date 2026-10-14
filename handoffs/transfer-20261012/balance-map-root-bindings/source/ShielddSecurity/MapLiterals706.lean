import ShielddSecurity.BalanceMapParameters699
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.MapLiterals706
open ConcreteJubjubField01 BalanceMapParameters699

def c1Literal : Nat := 9628519018340474679875156334893438995974717701127060143092098445975442038616
def c2Literal : Nat := 19676371192118968049803995723067767322369844622612809987311387700305851196142
def negativeC1Literal : Nat := 42807356156785715799572584173292526841715834799400577679511560253963139145897
def kLiteral : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581143549
def negativeLiteral : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184512

theorem c1_meaning : (c1Literal:F)=sourceC1 := by
  apply (mul_right_cancel₀ exact_map_coefficients_have_nonzero_k_and_c1.1)
  rw [exact_map_coefficient_products_recover_the_source_literals.1]
  decide +kernel

theorem c2_meaning : (c2Literal:F)=sourceC2 := by
  apply (mul_right_cancel₀ exact_map_coefficients_have_nonzero_k_and_c1.1)
  apply (mul_right_cancel₀ exact_map_coefficients_have_nonzero_k_and_c1.1)
  rw [exact_map_coefficient_products_recover_the_source_literals.2]
  decide +kernel

theorem negative_c1_meaning : (negativeC1Literal:F)= -sourceC1 := by
  rw [← c1_meaning]
  decide +kernel

theorem k_meaning : (kLiteral:F)=sourceK := by decide +kernel

theorem negative_meaning : (negativeLiteral:F)= -1 := by decide +kernel
end ShielddSecurity.MapLiterals706

set_option pp.all true in
#check @ShielddSecurity.MapLiterals706.c1_meaning
#print axioms ShielddSecurity.MapLiterals706.c1_meaning

set_option pp.all true in
#check @ShielddSecurity.MapLiterals706.c2_meaning
#print axioms ShielddSecurity.MapLiterals706.c2_meaning

set_option pp.all true in
#check @ShielddSecurity.MapLiterals706.negative_c1_meaning
#print axioms ShielddSecurity.MapLiterals706.negative_c1_meaning

set_option pp.all true in
#check @ShielddSecurity.MapLiterals706.k_meaning
#print axioms ShielddSecurity.MapLiterals706.k_meaning

set_option pp.all true in
#check @ShielddSecurity.MapLiterals706.negative_meaning
#print axioms ShielddSecurity.MapLiterals706.negative_meaning
