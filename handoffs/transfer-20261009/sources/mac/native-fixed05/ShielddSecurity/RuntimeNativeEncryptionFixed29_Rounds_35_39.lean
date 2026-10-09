import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step35 : states 36 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 35 (states 35) := by
  funext column
  fin_cases column <;> decide
theorem step36 : states 37 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 36 (states 36) := by
  funext column
  fin_cases column <;> decide
theorem step37 : states 38 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 37 (states 37) := by
  funext column
  fin_cases column <;> decide
theorem step38 : states 39 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 38 (states 38) := by
  funext column
  fin_cases column <;> decide
theorem step39 : states 40 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 39 (states 39) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step35
#print axioms step35
set_option pp.all true in
#check @step36
#print axioms step36
set_option pp.all true in
#check @step37
#print axioms step37
set_option pp.all true in
#check @step38
#print axioms step38
set_option pp.all true in
#check @step39
#print axioms step39
end ShielddSecurity.RuntimeNativeEncryptionFixed29
