import ShielddSecurity.TransferScalarSquareDiagonal01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSquareProduct01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSquareCross01 (sourceCrossWords crossValue)
open TransferScalarSquareShift01 (sourceDoubleWalk)
open TransferScalarSquareDiagonal01 (diagonalWalk diagonalValue)
/-! Join actual modeled cross MAC, doubling shifts, and diagonal MAC/ADC
steps. The full input square fits eight words and derives zero final carry,
so the source's discarded ADC carry is justified without a caller premise.
The exact wide Montgomery reducer then derives canonical square output. -/

def sourceSquareWide (self : Vector UInt64 4) : List UInt64 × UInt64 :=
  diagonalWalk self.toList 0 (sourceDoubleWalk 0 (sourceCrossWords self))

def sourceSquareMontgomery (self : Vector UInt64 4) : List UInt64 :=
  TransferScalarWideReduction01.sourceWideReduce (sourceSquareWide self).1

theorem source_square_cross_shift_diagonal_join_has_exact_full_integer (self : Vector UInt64 4) :
    (sourceSquareWide self).1.length = 8 ∧
      packWords (sourceSquareWide self).1 + radix64 ^ 8 * (sourceSquareWide self).2.toNat =
        packWords self.toList * packWords self.toList := by
  have shifted := TransferScalarSquareShift01.source_seven_word_cross_shift_retains_eight_words_and_exact_doubled_cross self
  have width : (sourceDoubleWalk 0 (sourceCrossWords self)).length = 2 * self.toList.length := by
    rw [shifted.1, Vector.length_toList]
  have contract := TransferScalarSquareDiagonal01.symbolic_diagonal_mac_adc_walk_derives_width_and_full_integer
    self.toList 0 (sourceDoubleWalk 0 (sourceCrossWords self)) width
  rw [Vector.length_toList, shifted.2, UInt64.toNat_zero, Nat.add_zero] at contract
  have identity := TransferScalarSquareDiagonal01.symbolic_diagonal_and_cross_values_reconstruct_exact_square self.toList
  have value : 2 * (radix64 * crossValue self.toList) + diagonalValue self.toList =
      packWords self.toList * packWords self.toList := by
    rw [identity]
    ac_rfl
  rw [value] at contract
  exact contract

theorem source_eight_word_square_derives_zero_discarded_adc_carry (self : Vector UInt64 4) :
    (sourceSquareWide self).1.length = 8 ∧ (sourceSquareWide self).2 = 0 ∧
      packWords (sourceSquareWide self).1 = packWords self.toList * packWords self.toList := by
  have contract := source_square_cross_shift_diagonal_join_has_exact_full_integer self
  have inputBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power self.toList
  rw [Vector.length_toList] at inputBound
  have productBound : packWords self.toList * packWords self.toList < radix64 ^ 8 := by
    have bound := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt inputBound) inputBound (by decide : 0 < radix64 ^ 4)
    have power : radix64 ^ 4 * radix64 ^ 4 = radix64 ^ 8 := (Nat.pow_add radix64 4 4).symm
    rw [power] at bound
    exact bound
  have carryZeroNat : (sourceSquareWide self).2.toNat = 0 := by
    by_cases zero : (sourceSquareWide self).2.toNat = 0
    · exact zero
    · have one : 1 ≤ (sourceSquareWide self).2.toNat := by omega
      have lower := Nat.mul_le_mul_left (radix64 ^ 8) one
      rw [Nat.mul_one] at lower
      omega
  have carryZero : (sourceSquareWide self).2 = 0 := UInt64.toNat_inj.mp carryZeroNat
  rw [carryZeroNat, Nat.mul_zero, Nat.add_zero] at contract
  exact ⟨contract.1, carryZero, contract.2⟩

theorem canonical_operand_source_square_derives_canonical_montgomery_contract
    (self : Vector UInt64 4) (canonical : packWords self.toList < TransferBoundedNativeCodec01.nullifierModulus) :
    (sourceSquareMontgomery self).length = 4 ∧
      packWords (sourceSquareMontgomery self) < TransferBoundedNativeCodec01.nullifierModulus ∧
      (radix64 ^ 4 * packWords (sourceSquareMontgomery self)) % TransferBoundedNativeCodec01.nullifierModulus =
        (packWords self.toList * packWords self.toList) % TransferBoundedNativeCodec01.nullifierModulus := by
  have product := source_eight_word_square_derives_zero_discarded_adc_carry self
  have rawBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power self.toList
  rw [Vector.length_toList] at rawBound
  have range := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt rawBound) canonical (by decide : 0 < radix64 ^ 4)
  have widened : packWords (sourceSquareWide self).1 <
      TransferBoundedNativeCodec01.nullifierModulus * (radix64 ^ 4 + 1) := by
    rw [product.2.2]
    have step := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self (radix64 ^ 4)) (by decide : 0 < TransferBoundedNativeCodec01.nullifierModulus)
    have strict : packWords self.toList * packWords self.toList <
        TransferBoundedNativeCodec01.nullifierModulus * radix64 ^ 4 := by
      simpa only [Nat.mul_comm] using range
    exact Nat.lt_trans strict step
  have contract := TransferScalarWideReduction01.source_wide_reduction_derives_width_canonical_range_and_modular_relation
    (sourceSquareWide self).1 product.1 widened
  rw [product.2.2] at contract
  exact contract

set_option pp.all true in
#check @sourceSquareWide
#print axioms sourceSquareWide
set_option pp.all true in
#check @sourceSquareMontgomery
#print axioms sourceSquareMontgomery
set_option pp.all true in
#check @source_square_cross_shift_diagonal_join_has_exact_full_integer
#print axioms source_square_cross_shift_diagonal_join_has_exact_full_integer
set_option pp.all true in
#check @source_eight_word_square_derives_zero_discarded_adc_carry
#print axioms source_eight_word_square_derives_zero_discarded_adc_carry
set_option pp.all true in
#check @canonical_operand_source_square_derives_canonical_montgomery_contract
#print axioms canonical_operand_source_square_derives_canonical_montgomery_contract
end ShielddSecurity.TransferScalarSquareProduct01
