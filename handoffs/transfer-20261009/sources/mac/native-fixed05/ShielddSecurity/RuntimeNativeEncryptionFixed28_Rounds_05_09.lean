import ShielddSecurity.RuntimeNativeEncryptionFixed28_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed28
theorem step05 : states 6 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 5 (states 5) := by
  funext column
  fin_cases column <;> decide
theorem step06 : states 7 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 6 (states 6) := by
  funext column
  fin_cases column <;> decide
theorem step07 : states 8 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 7 (states 7) := by
  funext column
  fin_cases column <;> decide
theorem step08 : states 9 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 8 (states 8) := by
  funext column
  fin_cases column <;> decide
theorem step09 : states 10 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 9 (states 9) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step05
#print axioms step05
set_option pp.all true in
#check @step06
#print axioms step06
set_option pp.all true in
#check @step07
#print axioms step07
set_option pp.all true in
#check @step08
#print axioms step08
set_option pp.all true in
#check @step09
#print axioms step09
end ShielddSecurity.RuntimeNativeEncryptionFixed28
