import ShielddSecurity.TransferScalarFourRoundWrapper01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarAdcShift01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (mac128 split128)
/-! Model of the pinned util.rs fixed 64-bit shift/casts and widened ADC.
The shift pair equals the proved quotient pair. ADC is a unit-multiplier MAC,
so its low/high words conserve the full sum. For the serializer's zero high
word and zero carry2, ADC retains the MAC carry with no overflow. These close
arithmetic model equations; Rust primitive/trace and SBB/endian remain separate. -/
def sourceSplit128 (ret : BitVec 128) : UInt64 × UInt64 :=
  (UInt64.ofNat ret.toNat, UInt64.ofNat ((ret >>> 64).toNat))
def adc128 (a b carry : UInt64) : BitVec 128 :=
  BitVec.ofNat 128 a.toNat + BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 carry.toNat
def adc64 (a b carry : UInt64) : UInt64 × UInt64 := sourceSplit128 (adc128 a b carry)

theorem fixed_high_shift_and_cast_equals_radix_quotient_pair (ret : BitVec 128) :
    sourceSplit128 ret = split128 ret := by
  unfold sourceSplit128 split128
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem widened_adc_is_unit_multiplier_mac (a b carry : UInt64) :
    adc128 a b carry = mac128 a 1 b carry := by
  change BitVec.ofNat 128 a.toNat + BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 carry.toNat =
    BitVec.ofNat 128 a.toNat + (1#128) * BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 carry.toNat
  rw [BitVec.one_mul]

theorem widened_adc_preserves_full_integer_sum (a b carry : UInt64) :
    (adc128 a b carry).toNat = a.toNat + b.toNat + carry.toNat := by
  rw [widened_adc_is_unit_multiplier_mac, TransferScalarWordPrimitives01.widened_u64_mac_preserves_full_integer,
    UInt64.toNat_one, Nat.one_mul]

theorem widened_adc_low_word_and_carry_conserve_sum (a b carry : UInt64) :
    (adc64 a b carry).1.toNat + radix64 * (adc64 a b carry).2.toNat = a.toNat + b.toNat + carry.toNat := by
  unfold adc64
  rw [fixed_high_shift_and_cast_equals_radix_quotient_pair,
    TransferScalarWordPrimitives01.split_double_word_preserves_full_integer, widened_adc_preserves_full_integer_sum]

theorem zero_upper_limb_adc_retains_carry_without_overflow (carry : UInt64) :
    adc64 0 0 carry = (carry, 0) := by
  unfold adc64
  rw [fixed_high_shift_and_cast_equals_radix_quotient_pair]
  unfold split128
  rw [widened_adc_preserves_full_integer_sum, UInt64.toNat_zero, Nat.zero_add]
  have bounded : carry.toNat < radix64 := carry.toNat_lt
  rw [UInt64.ofNat_toNat, Nat.div_eq_of_lt bounded]
  rfl

set_option pp.all true in
#check @sourceSplit128
#print axioms sourceSplit128
set_option pp.all true in
#check @adc128
#print axioms adc128
set_option pp.all true in
#check @adc64
#print axioms adc64
set_option pp.all true in
#check @fixed_high_shift_and_cast_equals_radix_quotient_pair
#print axioms fixed_high_shift_and_cast_equals_radix_quotient_pair
set_option pp.all true in
#check @widened_adc_is_unit_multiplier_mac
#print axioms widened_adc_is_unit_multiplier_mac
set_option pp.all true in
#check @widened_adc_preserves_full_integer_sum
#print axioms widened_adc_preserves_full_integer_sum
set_option pp.all true in
#check @widened_adc_low_word_and_carry_conserve_sum
#print axioms widened_adc_low_word_and_carry_conserve_sum
set_option pp.all true in
#check @zero_upper_limb_adc_retains_carry_without_overflow
#print axioms zero_upper_limb_adc_retains_carry_without_overflow
end ShielddSecurity.TransferScalarAdcShift01
