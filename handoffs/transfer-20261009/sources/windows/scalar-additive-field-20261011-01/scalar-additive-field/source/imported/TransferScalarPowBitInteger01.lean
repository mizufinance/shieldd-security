import ShielddSecurity.TransferScalarInvertField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPowBitInteger01
open TransferScalarPowInvariant01 (sourcePowBit)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
/-! Symbolic count/list recurrences connect the actual modeled UInt64
shift/mask bit test with binary digits and the reversed word/bit exponent
walk with its exact little-endian integer. No unrolled256-bit walk or caller
desired-exponent premise. Native primitive/compiler/caller binding is separate. -/

theorem bounded_source_word_shift_mask_has_exact_binary_digit
    (word : UInt64) (index : Nat) (bounded : index < 64) :
    ((word >>> UInt64.ofNat index) &&& 1).toNat = (word.toNat / 2 ^ index) % 2 := by
  have wide : index < 2 ^ 64 := Nat.lt_trans bounded (by decide : 64 < 2 ^ 64)
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt wide,
    Nat.mod_eq_of_lt bounded]
  change (word.toNat >>> index) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem bounded_source_word_boolean_bit_has_exact_binary_digit
    (word : UInt64) (index : Nat) (bounded : index < 64) :
    (if sourcePowBit word index then 1 else 0 : Nat) = (word.toNat / 2 ^ index) % 2 := by
  have selected : sourcePowBit word index = true ↔ (word.toNat / 2 ^ index) % 2 = 1 := by
    unfold sourcePowBit
    rw [beq_iff_eq, ← UInt64.toNat_inj]
    change ((word >>> UInt64.ofNat index) &&& 1).toNat = 1 ↔ _
    rw [bounded_source_word_shift_mask_has_exact_binary_digit word index bounded]
  have digitBound : (word.toNat / 2 ^ index) % 2 < 2 := Nat.mod_lt _ (by decide)
  cases bit : sourcePowBit word index with
  | false =>
    have notOne : (word.toNat / 2 ^ index) % 2 ≠ 1 := by
      intro one
      have yes := selected.mpr one
      rw [bit] at yes
      cases yes
    have zero : (word.toNat / 2 ^ index) % 2 = 0 := by omega
    exact zero.symm
  | true => exact (selected.mp bit).symm

theorem symbolic_high_to_low_binary_digit_walk_reconstructs_exact_low_bits
    (word count seed : Nat) :
    (List.range count).reverse.foldl (fun value index => value * 2 + (word / 2 ^ index) % 2) seed =
      seed * 2 ^ count + word % 2 ^ count := by
  induction count generalizing seed with
  | zero => simp only [List.range_zero, List.reverse_nil, List.foldl_nil, Nat.pow_zero,
      Nat.mul_one, Nat.mod_one, Nat.add_zero]
  | succ count ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.foldl_cons]
    rw [ih, Nat.mod_pow_succ, Nat.pow_succ, Nat.add_mul]
    ac_rfl

theorem symbolic_natural_folds_agree_from_actual_member_steps
    (items : List Nat) (seed : Nat) (left right : Nat → Nat → Nat)
    (agree : ∀ value index, index ∈ items → left value index = right value index) :
    items.foldl left seed = items.foldl right seed := by
  induction items generalizing seed with
  | nil => rfl
  | cons index rest ih =>
    change rest.foldl left (left seed index) = rest.foldl right (right seed index)
    rw [agree seed index (List.mem_cons_self)]
    apply ih
    intro value item inside
    exact agree value item (List.mem_cons_of_mem index inside)

theorem actual_source_word_bit_loop_reconstructs_exact_u64_integer
    (word : UInt64) (seed : Nat) :
    (List.range 64).reverse.foldl
      (fun value index => value * 2 + (if sourcePowBit word index then 1 else 0)) seed =
      seed * radix64 + word.toNat := by
  have coherent := symbolic_natural_folds_agree_from_actual_member_steps (List.range 64).reverse seed
    (fun value index => value * 2 + (if sourcePowBit word index then 1 else 0))
    (fun value index => value * 2 + (word.toNat / 2 ^ index) % 2)
    (by
      intro value index inside
      have bounded : index < 64 := List.mem_range.mp (List.mem_reverse.mp inside)
      dsimp only
      rw [bounded_source_word_boolean_bit_has_exact_binary_digit word index bounded])
  rw [coherent, symbolic_high_to_low_binary_digit_walk_reconstructs_exact_low_bits]
  have bounded : word.toNat < 2 ^ 64 := word.toNat_lt
  rw [Nat.mod_eq_of_lt bounded]
  rfl

theorem symbolic_source_reversed_word_bit_walk_reconstructs_exact_little_endian_integer
    (words : List UInt64) (seed : Nat) :
    words.reverse.foldl (fun value word => (List.range 64).reverse.foldl
      (fun current index => current * 2 + (if sourcePowBit word index then 1 else 0)) value) seed =
      seed * radix64 ^ words.length + packWords words := by
  induction words generalizing seed with
  | nil => simp only [List.reverse_nil, List.foldl_nil, List.length_nil, Nat.pow_zero,
      Nat.mul_one, packWords, Nat.add_zero]
  | cons word rest ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [actual_source_word_bit_loop_reconstructs_exact_u64_integer]
    change (seed * radix64 ^ rest.length + packWords rest) * radix64 + word.toNat =
      seed * radix64 ^ (rest.length + 1) + (word.toNat + radix64 * packWords rest)
    rw [Nat.pow_succ, Nat.add_mul]
    ac_rfl

set_option pp.all true in
#check @bounded_source_word_shift_mask_has_exact_binary_digit
#print axioms bounded_source_word_shift_mask_has_exact_binary_digit
set_option pp.all true in
#check @bounded_source_word_boolean_bit_has_exact_binary_digit
#print axioms bounded_source_word_boolean_bit_has_exact_binary_digit
set_option pp.all true in
#check @symbolic_high_to_low_binary_digit_walk_reconstructs_exact_low_bits
#print axioms symbolic_high_to_low_binary_digit_walk_reconstructs_exact_low_bits
set_option pp.all true in
#check @symbolic_natural_folds_agree_from_actual_member_steps
#print axioms symbolic_natural_folds_agree_from_actual_member_steps
set_option pp.all true in
#check @actual_source_word_bit_loop_reconstructs_exact_u64_integer
#print axioms actual_source_word_bit_loop_reconstructs_exact_u64_integer
set_option pp.all true in
#check @symbolic_source_reversed_word_bit_walk_reconstructs_exact_little_endian_integer
#print axioms symbolic_source_reversed_word_bit_walk_reconstructs_exact_little_endian_integer
end ShielddSecurity.TransferScalarPowBitInteger01
