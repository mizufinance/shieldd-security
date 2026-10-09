import ShielddSecurity.RuntimeNativeEncryptionFixed29_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed29
theorem step30 : states 31 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 30 (states 30) := by
  funext column
  fin_cases column <;> decide
theorem step31 : states 32 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 31 (states 31) := by
  funext column
  fin_cases column <;> decide
theorem step32 : states 33 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 32 (states 32) := by
  funext column
  fin_cases column <;> decide
theorem step33 : states 34 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 33 (states 33) := by
  funext column
  fin_cases column <;> decide
theorem step34 : states 35 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 34 (states 34) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step30
#print axioms step30
set_option pp.all true in
#check @step31
#print axioms step31
set_option pp.all true in
#check @step32
#print axioms step32
set_option pp.all true in
#check @step33
#print axioms step33
set_option pp.all true in
#check @step34
#print axioms step34
end ShielddSecurity.RuntimeNativeEncryptionFixed29
