import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step50 : states 51 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 50 (states 50) := by
  funext column
  fin_cases column <;> decide
theorem step51 : states 52 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 51 (states 51) := by
  funext column
  fin_cases column <;> decide
theorem step52 : states 53 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 52 (states 52) := by
  funext column
  fin_cases column <;> decide
theorem step53 : states 54 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 53 (states 53) := by
  funext column
  fin_cases column <;> decide
theorem step54 : states 55 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 54 (states 54) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step50
#print axioms step50
set_option pp.all true in
#check @step51
#print axioms step51
set_option pp.all true in
#check @step52
#print axioms step52
set_option pp.all true in
#check @step53
#print axioms step53
set_option pp.all true in
#check @step54
#print axioms step54
end ShielddSecurity.RuntimeNativeEncryptionFixed29
