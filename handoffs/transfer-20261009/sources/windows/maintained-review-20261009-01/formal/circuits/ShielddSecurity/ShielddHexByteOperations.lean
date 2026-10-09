import Init.Data.UInt.Bitwise
import ShielddSecurity.ShielddHexCodec

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexByteOperations

def lowerTable : List Nat := [48,49,50,51,52,53,54,55,56,57,97,98,99,100,101,102]

theorem lower_table : ∀ index : Fin 16,
    lowerTable.get index = ShielddHexCodec.lowerDigit index.val := by decide

/- These universal finite-byte identities give the shift/mask/OR arithmetic
used by the pinned hex algorithm source view. They use Lean's unsigned-byte
operations, not an assumed per-byte answer or external hex roundtrip law. -/
theorem high_nibble (byte : UInt8) :
    (byte >>> (4 : UInt8)).toNat = byte.toNat / 16 := by
  rw [UInt8.toNat_shiftRight]
  change (byte.toNat >>> 4) = byte.toNat / 16
  rw [Nat.shiftRight_eq_div_pow]

theorem low_nibble (byte : UInt8) :
    (byte &&& (15 : UInt8)).toNat = byte.toNat % 16 := by
  rw [UInt8.toNat_and]
  change (byte.toNat &&& (2 ^ 4 - 1)) = byte.toNat % 2 ^ 4
  exact Nat.and_two_pow_sub_one_eq_mod byte.toNat 4

theorem pair_join (high low : UInt8)
    (highBound : high.toNat < 16) (lowBound : low.toNat < 16) :
    ((high <<< (4 : UInt8)) ||| low).toNat = 16 * high.toNat + low.toNat := by
  rw [UInt8.toNat_or, UInt8.toNat_shiftLeft]
  change ((high.toNat <<< 4) % 256) ||| low.toNat = 16 * high.toNat + low.toNat
  rw [Nat.shiftLeft_eq]
  have bounded : high.toNat * 16 < 256 := by omega
  change (high.toNat * 16 % 256) ||| low.toNat = _
  rw [Nat.mod_eq_of_lt bounded]
  have join : 16 * high.toNat + low.toNat = (16 * high.toNat) ||| low.toNat :=
    Nat.two_pow_add_eq_or_of_lt (i := 4) lowBound high.toNat
  rw [Nat.mul_comm high.toNat 16]
  exact join.symm

set_option pp.all true in
#check @lower_table
#print axioms lower_table
set_option pp.all true in
#check @high_nibble
#print axioms high_nibble
set_option pp.all true in
#check @low_nibble
#print axioms low_nibble
set_option pp.all true in
#check @pair_join
#print axioms pair_join

end ShielddSecurity.ShielddHexByteOperations
