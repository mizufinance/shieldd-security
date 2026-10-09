import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step20 : states 21 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 20 (states 20) := by
  funext column
  fin_cases column <;> decide
theorem step21 : states 22 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 21 (states 21) := by
  funext column
  fin_cases column <;> decide
theorem step22 : states 23 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 22 (states 22) := by
  funext column
  fin_cases column <;> decide
theorem step23 : states 24 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 23 (states 23) := by
  funext column
  fin_cases column <;> decide
theorem step24 : states 25 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 24 (states 24) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step20
#print axioms step20
set_option pp.all true in
#check @step21
#print axioms step21
set_option pp.all true in
#check @step22
#print axioms step22
set_option pp.all true in
#check @step23
#print axioms step23
set_option pp.all true in
#check @step24
#print axioms step24
end ShielddSecurity.RuntimeNativeEncryptionFixed29
