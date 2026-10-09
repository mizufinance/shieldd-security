import ShielddSecurity.RuntimeNativeEncryptionFixed28_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeNativeEncryptionFixed28
theorem step60 : states 61 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 60 (states 60) := by
  funext column
  fin_cases column <;> decide
theorem step61 : states 62 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 61 (states 61) := by
  funext column
  fin_cases column <;> decide
theorem step62 : states 63 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 62 (states 62) := by
  funext column
  fin_cases column <;> decide
theorem step63 : states 64 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 63 (states 63) := by
  funext column
  fin_cases column <;> decide
theorem step64 : states 65 =
    NativeEncryptionFixedArithmetic.integerRound RuntimeHashBlock_authorization_rnk_permutation2_0.parameters 64 (states 64) := by
  funext column
  fin_cases column <;> decide
set_option pp.all true in
#check @step60
#print axioms step60
set_option pp.all true in
#check @step61
#print axioms step61
set_option pp.all true in
#check @step62
#print axioms step62
set_option pp.all true in
#check @step63
#print axioms step63
set_option pp.all true in
#check @step64
#print axioms step64
end ShielddSecurity.RuntimeNativeEncryptionFixed28
