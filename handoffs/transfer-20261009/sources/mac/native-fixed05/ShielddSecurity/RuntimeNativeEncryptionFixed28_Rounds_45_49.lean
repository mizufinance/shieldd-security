import ShielddSecurity.RuntimeNativeEncryptionFixed28_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed28
theorem step45 : states 46 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 45 (states 45) := by
  funext column
  fin_cases column <;> decide
theorem step46 : states 47 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 46 (states 46) := by
  funext column
  fin_cases column <;> decide
theorem step47 : states 48 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 47 (states 47) := by
  funext column
  fin_cases column <;> decide
theorem step48 : states 49 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 48 (states 48) := by
  funext column
  fin_cases column <;> decide
theorem step49 : states 50 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 49 (states 49) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step45
#print axioms step45
set_option pp.all true in
#check @step46
#print axioms step46
set_option pp.all true in
#check @step47
#print axioms step47
set_option pp.all true in
#check @step48
#print axioms step48
set_option pp.all true in
#check @step49
#print axioms step49
end ShielddSecurity.RuntimeNativeEncryptionFixed28
