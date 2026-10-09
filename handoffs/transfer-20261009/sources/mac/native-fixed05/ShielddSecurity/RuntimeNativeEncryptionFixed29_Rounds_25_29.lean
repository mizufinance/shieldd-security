import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step25 : states 26 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 25 (states 25) := by
  funext column
  fin_cases column <;> decide
theorem step26 : states 27 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 26 (states 26) := by
  funext column
  fin_cases column <;> decide
theorem step27 : states 28 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 27 (states 27) := by
  funext column
  fin_cases column <;> decide
theorem step28 : states 29 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 28 (states 28) := by
  funext column
  fin_cases column <;> decide
theorem step29 : states 30 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 29 (states 29) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step25
#print axioms step25
set_option pp.all true in
#check @step26
#print axioms step26
set_option pp.all true in
#check @step27
#print axioms step27
set_option pp.all true in
#check @step28
#print axioms step28
set_option pp.all true in
#check @step29
#print axioms step29
end ShielddSecurity.RuntimeNativeEncryptionFixed29
