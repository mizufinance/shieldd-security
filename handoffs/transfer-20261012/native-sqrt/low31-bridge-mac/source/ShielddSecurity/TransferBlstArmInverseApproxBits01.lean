import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseApproxBits01

/-! Narrow exact low31 replacement arithmetic and oddness; high-window selection, full-input rows, approximate progress and native execution remain separate. -/

def sourceApproxLow31 (high low : UInt64) : Nat :=
  high.toNat/2147483648*2147483648+low.toNat%2147483648

theorem original_approximation_replacement_retains_all_31_low_bits (high low : UInt64) :
    sourceApproxLow31 high low%2147483648=low.toNat%2147483648 := by
  unfold sourceApproxLow31
  simp only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_mod,Nat.zero_add,Nat.mod_mod]

theorem original_low31_approximation_preserves_oddness_of_the_original_low_word
    (high low : UInt64) (odd : low.toNat%2=1) :
    sourceApproxLow31 high low%2=1 := by
  have evenScale : (2147483648:Nat)%2=0 := by decide
  have divisor : (2:Nat) ∣ 2147483648 := ⟨1073741824,by decide⟩
  unfold sourceApproxLow31
  rw [Nat.add_mod,Nat.mul_mod,evenScale,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,
    Nat.mod_mod_of_dvd low.toNat divisor,odd]

set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseApproxBits01.sourceApproxLow31
#print axioms ShielddSecurity.TransferBlstArmInverseApproxBits01.sourceApproxLow31
set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseApproxBits01.original_approximation_replacement_retains_all_31_low_bits
#print axioms ShielddSecurity.TransferBlstArmInverseApproxBits01.original_approximation_replacement_retains_all_31_low_bits
set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word
#print axioms ShielddSecurity.TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word
end ShielddSecurity.TransferBlstArmInverseApproxBits01
