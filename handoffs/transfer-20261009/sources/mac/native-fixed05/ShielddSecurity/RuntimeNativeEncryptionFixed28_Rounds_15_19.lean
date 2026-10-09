import ShielddSecurity.RuntimeNativeEncryptionFixed28_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed28
theorem step15 : states 16 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 15 (states 15) := by
  funext column
  fin_cases column <;> decide
theorem step16 : states 17 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 16 (states 16) := by
  funext column
  fin_cases column <;> decide
theorem step17 : states 18 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 17 (states 17) := by
  funext column
  fin_cases column <;> decide
theorem step18 : states 19 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 18 (states 18) := by
  funext column
  fin_cases column <;> decide
theorem step19 : states 20 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 19 (states 19) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step15
#print axioms step15
set_option pp.all true in
#check @step16
#print axioms step16
set_option pp.all true in
#check @step17
#print axioms step17
set_option pp.all true in
#check @step18
#print axioms step18
set_option pp.all true in
#check @step19
#print axioms step19
end ShielddSecurity.RuntimeNativeEncryptionFixed28
