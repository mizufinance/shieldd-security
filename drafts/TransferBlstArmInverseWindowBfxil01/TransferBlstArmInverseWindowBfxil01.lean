import Init.Data.UInt.Lemmas
import Init.Data.BitVec.Lemmas
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowBfxil01

/-! UNRUN handwritten typed bitfield replacement used by BFXIL #0,#31.
The original high33 and low31 fragments are extracted and concatenated.
This proves the mathematical primitive; decoding/executing the compiled
instruction and caller register provenance remain separate obligations. -/

def sourceWindowLow31Word (high low : UInt64) : UInt64 :=
  UInt64.ofBitVec ((high.toBitVec.extractLsb' 31 33).append (low.toBitVec.extractLsb' 0 31))

theorem original_typed_low31_bitfield_replacement_has_its_entire_nat_value
    (high low : UInt64) :
    (sourceWindowLow31Word high low).toNat =
      high.toNat / 2 ^ 31 * 2 ^ 31 + low.toNat % 2 ^ 31 := by
  have highBound : high.toNat / 2 ^ 31 < 2 ^ 33 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 31)).2
    have split : (2 : Nat) ^ 33 * 2 ^ 31 = 2 ^ 64 := by rw [← Nat.pow_add]
    rw [split]
    exact high.toNat_lt
  have lowBound : low.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (Nat.two_pow_pos 31)
  rw [sourceWindowLow31Word, UInt64.toNat_ofBitVec, BitVec.toNat_append]
  simp only [BitVec.extractLsb'_toNat, UInt64.toNat_toBitVec,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt highBound, ← Nat.shiftLeft_add_eq_or_of_lt lowBound, Nat.shiftLeft_eq]

theorem original_typed_low31_bitfield_replacement_preserves_all_original_low_bits
    (high low : UInt64) :
    (sourceWindowLow31Word high low).toNat % 2 ^ 31 = low.toNat % 2 ^ 31 := by
  rw [original_typed_low31_bitfield_replacement_has_its_entire_nat_value]
  simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]

theorem original_entire_low31_replacement_value_fits_its_unsigned_word
    (high low : UInt64) :
    high.toNat / 2 ^ 31 * 2 ^ 31 + low.toNat % 2 ^ 31 < 2 ^ 64 := by
  rw [← original_typed_low31_bitfield_replacement_has_its_entire_nat_value]
  exact (sourceWindowLow31Word high low).toNat_lt

end ShielddSecurity.TransferBlstArmInverseWindowBfxil01
