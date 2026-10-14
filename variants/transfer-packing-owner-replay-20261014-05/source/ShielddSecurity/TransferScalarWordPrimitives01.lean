import ShielddSecurity.TransferScalarSerializationRange01
import Init.Data.BitVec.Lemmas
import Init.Data.UInt.Lemmas
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWordPrimitives01
open TransferScalarSerializationRange01 (radix64 reduceRounds normalize)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact finite-word arithmetic model for the pinned scalar util.rs operations.
u64 packing supplies the raw range premise; a widened 128-bit MAC is proved
nonoverflowing and its low/high u64 split conserves the full integer value.
These Lean UInt64/BitVec semantics still require correspondence to Rust
primitive evaluation and the actual four-round carry schedule and sub/byte
layout. Registry source identity is not semantic proof or runtime testing. -/
def packWords : List UInt64 → Nat
  | [] => 0
  | word :: rest => word.toNat + radix64 * packWords rest

def mac128 (a b c carry : UInt64) : BitVec 128 :=
  BitVec.ofNat 128 a.toNat + BitVec.ofNat 128 b.toNat * BitVec.ofNat 128 c.toNat + BitVec.ofNat 128 carry.toNat

def split128 (ret : BitVec 128) : UInt64 × UInt64 :=
  (UInt64.ofNat ret.toNat, UInt64.ofNat (ret.toNat / radix64))

def scalarReduction (raw multipliers : List UInt64) : Nat :=
  normalize nullifierModulus (reduceRounds nullifierModulus radix64 (packWords raw) (multipliers.map UInt64.toNat))

theorem packed_u64_vector_is_below_radix_power (words : List UInt64) :
    packWords words < radix64 ^ words.length := by
  induction words with
  | nil => decide
  | cons word rest ih =>
    change word.toNat + radix64 * packWords rest < radix64 ^ (rest.length + 1)
    calc
      word.toNat + radix64 * packWords rest < radix64 + radix64 * packWords rest :=
        Nat.add_lt_add_right word.toNat_lt _
      _ = radix64 * (packWords rest + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ radix64 * radix64 ^ rest.length := Nat.mul_le_mul_left radix64 (Nat.succ_le_of_lt ih)
      _ = radix64 ^ (rest.length + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem multiply_accumulate_of_four_words_fits_double_width
    (radix a b c carry : Nat) (positive : 0 < radix)
    (ha : a < radix) (hb : b < radix) (hc : c < radix) (hd : carry < radix) :
    a + b * c + carry < radix * radix := by
  have upper : a + b * c + carry ≤ (radix - 1) + (radix - 1) * (radix - 1) + (radix - 1) :=
    Nat.add_le_add (Nat.add_le_add (Nat.le_sub_one_of_lt ha)
      (Nat.mul_le_mul (Nat.le_sub_one_of_lt hb) (Nat.le_sub_one_of_lt hc))) (Nat.le_sub_one_of_lt hd)
  have square : (radix - 1) + (radix - 1) * (radix - 1) + (radix - 1) + 1 = radix * radix := by
    calc
      _ = ((radix - 1) + 1) * ((radix - 1) + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = radix * radix := by rw [Nat.sub_add_cancel positive]
  exact Nat.lt_of_le_of_lt upper (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) square)

theorem widened_u64_mac_preserves_full_integer (a b c carry : UInt64) :
    (mac128 a b c carry).toNat = a.toNat + b.toNat * c.toNat + carry.toNat := by
  have bounded := multiply_accumulate_of_four_words_fits_double_width radix64
    a.toNat b.toNat c.toNat carry.toNat (by decide) a.toNat_lt b.toNat_lt c.toNat_lt carry.toNat_lt
  change (((a.toNat % 2 ^ 128 + (b.toNat % 2 ^ 128 * (c.toNat % 2 ^ 128)) % 2 ^ 128) % 2 ^ 128) + carry.toNat % 2 ^ 128) % 2 ^ 128 = _
  simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]
  exact Nat.mod_eq_of_lt bounded

theorem split_double_word_preserves_full_integer (ret : BitVec 128) :
    (split128 ret).1.toNat + radix64 * (split128 ret).2.toNat = ret.toNat := by
  have bounded : ret.toNat < radix64 * radix64 := ret.isLt
  have carryBound : ret.toNat / radix64 < radix64 := (Nat.div_lt_iff_lt_mul (by decide)).2 bounded
  change ret.toNat % radix64 + radix64 * ((ret.toNat / radix64) % radix64) = ret.toNat
  rw [Nat.mod_eq_of_lt carryBound]
  exact Nat.mod_add_div ret.toNat radix64

theorem widened_u64_mac_low_word_and_carry_conserve_value (a b c carry : UInt64) :
    (split128 (mac128 a b c carry)).1.toNat + radix64 * (split128 (mac128 a b c carry)).2.toNat =
      a.toNat + b.toNat * c.toNat + carry.toNat := by
  rw [split_double_word_preserves_full_integer, widened_u64_mac_preserves_full_integer]

theorem four_actual_u64_inputs_and_multipliers_reduce_into_canonical_field
    (raw multipliers : List UInt64) (fourRaw : raw.length = 4) (fourMultipliers : multipliers.length = 4) :
    scalarReduction raw multipliers < nullifierModulus := by
  apply TransferScalarSerializationRange01.final_subtraction_is_canonical nullifierModulus _ (by decide)
  apply TransferScalarSerializationRange01.all_rounds_finish_at_most_modulus nullifierModulus radix64
    (multipliers.map UInt64.toNat) (by decide)
  · intro digit inside
    obtain ⟨word, _, value⟩ := List.mem_map.mp inside
    subst digit
    exact word.toNat_lt
  · have bounded := packed_u64_vector_is_below_radix_power raw
    rw [List.length_map, fourMultipliers]
    rw [fourRaw] at bounded
    exact Nat.lt_of_lt_of_le bounded (Nat.le_add_left _ _)

set_option pp.all true in
#check @packWords
#print axioms packWords
set_option pp.all true in
#check @mac128
#print axioms mac128
set_option pp.all true in
#check @split128
#print axioms split128
set_option pp.all true in
#check @scalarReduction
#print axioms scalarReduction
set_option pp.all true in
#check @packed_u64_vector_is_below_radix_power
#print axioms packed_u64_vector_is_below_radix_power
set_option pp.all true in
#check @multiply_accumulate_of_four_words_fits_double_width
#print axioms multiply_accumulate_of_four_words_fits_double_width
set_option pp.all true in
#check @widened_u64_mac_preserves_full_integer
#print axioms widened_u64_mac_preserves_full_integer
set_option pp.all true in
#check @split_double_word_preserves_full_integer
#print axioms split_double_word_preserves_full_integer
set_option pp.all true in
#check @widened_u64_mac_low_word_and_carry_conserve_value
#print axioms widened_u64_mac_low_word_and_carry_conserve_value
set_option pp.all true in
#check @four_actual_u64_inputs_and_multipliers_reduce_into_canonical_field
#print axioms four_actual_u64_inputs_and_multipliers_reduce_into_canonical_field
end ShielddSecurity.TransferScalarWordPrimitives01
