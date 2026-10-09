import ShielddSecurity.ScalarBits
import Init.Data.Nat.Bitwise.Lemmas

set_option maxHeartbeats 300000

namespace ShielddSecurity.RoutingSuffixCodec

/-- Mathematical byte contents of the upstream canonical 32-byte big-endian
scalar encoding. Its functional contract must be connected at the caller. -/
def canonicalByte (value index : Nat) : Nat := value / 256 ^ (31 - index) % 256

/-- Owned bytes[28..32] and u32::from_be_bytes in their exact source order. -/
def suffixWord (value : Nat) : Nat :=
  ((canonicalByte value 28 * 256 + canonicalByte value 29) * 256 +
    canonicalByte value 30) * 256 + canonicalByte value 31

theorem suffix_residue (value : Nat) : suffixWord value = value % 2 ^ 32 := by
  simp only [suffixWord, canonicalByte]
  norm_num
  omega

theorem suffix_bound (value : Nat) : suffixWord value < 2 ^ 32 := by
  rw [suffix_residue]
  exact Nat.mod_lt value (by decide)

theorem suffix_bit (value : Nat) (bit : Fin 32) :
    decide (suffixWord value / 2 ^ bit.val % 2 = 1) =
      decide (value / 2 ^ bit.val % 2 = 1) := by
  rw [suffix_residue]
  simp only [← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_mod_two_pow,
    bit.isLt, decide_true, Bool.true_and]

set_option pp.all true in
#check @suffix_residue
#print axioms suffix_residue
set_option pp.all true in
#check @suffix_bound
#print axioms suffix_bound
set_option pp.all true in
#check @suffix_bit
#print axioms suffix_bit

end ShielddSecurity.RoutingSuffixCodec
