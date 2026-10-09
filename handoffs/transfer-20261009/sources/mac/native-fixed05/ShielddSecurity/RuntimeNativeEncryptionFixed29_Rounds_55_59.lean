import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step55 : states 56 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 55 (states 55) := by
  funext column
  fin_cases column <;> decide
theorem step56 : states 57 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 56 (states 56) := by
  funext column
  fin_cases column <;> decide
theorem step57 : states 58 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 57 (states 57) := by
  funext column
  fin_cases column <;> decide
theorem step58 : states 59 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 58 (states 58) := by
  funext column
  fin_cases column <;> decide
theorem step59 : states 60 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 59 (states 59) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step55
#print axioms step55
set_option pp.all true in
#check @step56
#print axioms step56
set_option pp.all true in
#check @step57
#print axioms step57
set_option pp.all true in
#check @step58
#print axioms step58
set_option pp.all true in
#check @step59
#print axioms step59
end ShielddSecurity.RuntimeNativeEncryptionFixed29
