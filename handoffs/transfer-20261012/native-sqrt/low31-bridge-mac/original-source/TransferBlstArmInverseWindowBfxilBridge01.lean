import ShielddSecurity.TransferBlstArmInverseWindowBfxil01
import ShielddSecurity.TransferBlstArmInverseApproxBits01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowBfxilBridge01
open TransferBlstArmInverseWindowBfxil01 (sourceWindowLow31Word)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)

/-! UNRUN explicit bridge to the existing original low31 approximation model.
Its meaning is retained exactly; native BFXIL execution and register caller
correspondence remain open. -/

theorem original_typed_bfxil_word_observation_is_the_existing_low31_approximation
    (high low : UInt64) : (sourceWindowLow31Word high low).toNat = sourceApproxLow31 high low := by
  rw [TransferBlstArmInverseWindowBfxil01.original_typed_low31_bitfield_replacement_has_its_entire_nat_value]
  have scale : (2 : Nat) ^ 31 = 2147483648 := by decide +kernel
  simp only [sourceApproxLow31, scale]

theorem original_typed_bfxil_approximation_retains_oddness_from_the_original_low_word
    (high low : UInt64) (odd : low.toNat % 2 = 1) :
    (sourceWindowLow31Word high low).toNat % 2 = 1 := by
  rw [original_typed_bfxil_word_observation_is_the_existing_low31_approximation]
  exact TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word high low odd

end ShielddSecurity.TransferBlstArmInverseWindowBfxilBridge01
