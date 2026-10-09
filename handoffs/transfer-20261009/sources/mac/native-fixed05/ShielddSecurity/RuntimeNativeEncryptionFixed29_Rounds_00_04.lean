import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step00 : states 1 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 0 (states 0) := by
  funext column
  fin_cases column <;> decide
theorem step01 : states 2 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 1 (states 1) := by
  funext column
  fin_cases column <;> decide
theorem step02 : states 3 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 2 (states 2) := by
  funext column
  fin_cases column <;> decide
theorem step03 : states 4 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 3 (states 3) := by
  funext column
  fin_cases column <;> decide
theorem step04 : states 5 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 4 (states 4) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step00
#print axioms step00
set_option pp.all true in
#check @step01
#print axioms step01
set_option pp.all true in
#check @step02
#print axioms step02
set_option pp.all true in
#check @step03
#print axioms step03
set_option pp.all true in
#check @step04
#print axioms step04
end ShielddSecurity.RuntimeNativeEncryptionFixed29
