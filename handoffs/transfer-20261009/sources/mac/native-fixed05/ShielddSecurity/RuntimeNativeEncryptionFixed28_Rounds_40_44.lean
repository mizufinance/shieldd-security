import ShielddSecurity.RuntimeNativeEncryptionFixed28_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed28
theorem step40 : states 41 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 40 (states 40) := by
  funext column
  fin_cases column <;> decide
theorem step41 : states 42 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 41 (states 41) := by
  funext column
  fin_cases column <;> decide
theorem step42 : states 43 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 42 (states 42) := by
  funext column
  fin_cases column <;> decide
theorem step43 : states 44 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 43 (states 43) := by
  funext column
  fin_cases column <;> decide
theorem step44 : states 45 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 44 (states 44) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step40
#print axioms step40
set_option pp.all true in
#check @step41
#print axioms step41
set_option pp.all true in
#check @step42
#print axioms step42
set_option pp.all true in
#check @step43
#print axioms step43
set_option pp.all true in
#check @step44
#print axioms step44
end ShielddSecurity.RuntimeNativeEncryptionFixed28
