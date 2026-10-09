import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step10 : states 11 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 10 (states 10) := by
  funext column
  fin_cases column <;> decide
theorem step11 : states 12 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 11 (states 11) := by
  funext column
  fin_cases column <;> decide
theorem step12 : states 13 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 12 (states 12) := by
  funext column
  fin_cases column <;> decide
theorem step13 : states 14 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 13 (states 13) := by
  funext column
  fin_cases column <;> decide
theorem step14 : states 15 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 14 (states 14) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step10
#print axioms step10
set_option pp.all true in
#check @step11
#print axioms step11
set_option pp.all true in
#check @step12
#print axioms step12
set_option pp.all true in
#check @step13
#print axioms step13
set_option pp.all true in
#check @step14
#print axioms step14
end ShielddSecurity.RuntimeNativeEncryptionFixed29
