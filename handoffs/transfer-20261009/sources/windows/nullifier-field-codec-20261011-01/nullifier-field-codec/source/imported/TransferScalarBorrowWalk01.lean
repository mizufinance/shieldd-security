import ShielddSecurity.TransferScalarSbbPrimitive01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarBorrowWalk01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSbbPrimitive01 (borrowMask borrowBit sbb64)
/-! Symbolic finite borrow walk over actual source-shaped SBB low limbs.
Each next Bool encodes the exact outgoing zero/all-ones source borrow mask,
proved from the primitive, and is fed into the next call. Conservation and
finite output bounds derive final underflow; no desired borrow outcome is
supplied. Rust trace, whole add-back and byte layout remain interfaces. -/
def nextBorrow (a b : UInt64) (borrow : Bool) : Bool :=
  if a.toNat < b.toNat + borrowBit borrow then true else false
def borrowWalk (borrow : Bool) : List (UInt64 × UInt64) → List UInt64 × Bool
  | [] => ([], borrow)
  | pair :: rest =>
    let step := sbb64 pair.1 pair.2 borrow
    let after := borrowWalk (nextBorrow pair.1 pair.2 borrow) rest
    (step.1 :: after.1, after.2)

theorem computed_next_borrow_encodes_actual_source_mask (a b : UInt64) (borrow : Bool) :
    (sbb64 a b borrow).2 = borrowMask (nextBorrow a b borrow) := by
  have exactMask := (TransferScalarSbbPrimitive01.source_sbb_low_word_and_next_borrow_mask_are_exact a b borrow).1
  by_cases underflow : a.toNat < b.toNat + borrowBit borrow
  · rw [nextBorrow, if_pos underflow]
    simpa only [if_pos underflow] using exactMask
  · rw [nextBorrow, if_neg underflow]
    simpa only [if_neg underflow] using exactMask

theorem computed_next_borrow_preserves_primitive_subtraction_equation (a b : UInt64) (borrow : Bool) :
    (sbb64 a b borrow).1.toNat + b.toNat + borrowBit borrow =
      a.toNat + radix64 * borrowBit (nextBorrow a b borrow) := by
  have conserved := (TransferScalarSbbPrimitive01.source_sbb_low_word_and_next_borrow_mask_are_exact a b borrow).2
  by_cases underflow : a.toNat < b.toNat + borrowBit borrow
  · rw [nextBorrow, if_pos underflow]
    simpa only [if_pos underflow] using conserved
  · rw [nextBorrow, if_neg underflow]
    simpa only [if_neg underflow] using conserved

theorem borrow_walk_retains_limb_count (borrow : Bool) (pairs : List (UInt64 × UInt64)) :
    (borrowWalk borrow pairs).1.length = pairs.length := by
  induction pairs generalizing borrow with
  | nil => rfl
  | cons pair rest ih =>
    change (borrowWalk (nextBorrow pair.1 pair.2 borrow) rest).1.length + 1 = rest.length + 1
    rw [ih]

theorem borrow_walk_conserves_full_subtraction_equation (borrow : Bool) (pairs : List (UInt64 × UInt64)) :
    packWords (borrowWalk borrow pairs).1 + packWords (pairs.map Prod.snd) + borrowBit borrow =
      packWords (pairs.map Prod.fst) + radix64 ^ pairs.length * borrowBit (borrowWalk borrow pairs).2 := by
  induction pairs generalizing borrow with
  | nil => simp [borrowWalk, packWords, borrowBit]
  | cons pair rest ih =>
    let next := nextBorrow pair.1 pair.2 borrow
    let step := sbb64 pair.1 pair.2 borrow
    let after := borrowWalk next rest
    have tail := ih next
    have first := computed_next_borrow_preserves_primitive_subtraction_equation pair.1 pair.2 borrow
    change (step.1.toNat + radix64 * packWords after.1) +
      (pair.2.toNat + radix64 * packWords (rest.map Prod.snd)) + borrowBit borrow =
      (pair.1.toNat + radix64 * packWords (rest.map Prod.fst)) +
        radix64 ^ (rest.length + 1) * borrowBit after.2
    calc
      _ = (step.1.toNat + pair.2.toNat + borrowBit borrow) + radix64 * packWords after.1 + radix64 * packWords (rest.map Prod.snd) := by ac_rfl
      _ = (pair.1.toNat + radix64 * borrowBit next) + radix64 * packWords after.1 + radix64 * packWords (rest.map Prod.snd) := by rw [first]
      _ = pair.1.toNat + radix64 * (packWords after.1 + packWords (rest.map Prod.snd) + borrowBit next) := by
        rw [Nat.mul_add, Nat.mul_add]
        ac_rfl
      _ = pair.1.toNat + radix64 * (packWords (rest.map Prod.fst) + radix64 ^ rest.length * borrowBit after.2) := by rw [tail]
      _ = _ := by
        rw [Nat.pow_succ, Nat.mul_add]
        ac_rfl

theorem final_borrow_is_exact_input_underflow (pairs : List (UInt64 × UInt64)) :
    (borrowWalk false pairs).2 = true ↔ packWords (pairs.map Prod.fst) < packWords (pairs.map Prod.snd) := by
  have conserved := borrow_walk_conserves_full_subtraction_equation false pairs
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (borrowWalk false pairs).1
  rw [borrow_walk_retains_limb_count] at bounded
  cases final : (borrowWalk false pairs).2 with
  | false =>
    simp [borrowBit, final] at conserved
    constructor
    · intro impossible
      cases impossible
    · intro underflow
      omega
  | true =>
    simp [borrowBit, final] at conserved
    constructor
    · intro _
      omega
    · intro _
      rfl

set_option pp.all true in
#check @nextBorrow
#print axioms nextBorrow
set_option pp.all true in
#check @borrowWalk
#print axioms borrowWalk
set_option pp.all true in
#check @computed_next_borrow_encodes_actual_source_mask
#print axioms computed_next_borrow_encodes_actual_source_mask
set_option pp.all true in
#check @computed_next_borrow_preserves_primitive_subtraction_equation
#print axioms computed_next_borrow_preserves_primitive_subtraction_equation
set_option pp.all true in
#check @borrow_walk_retains_limb_count
#print axioms borrow_walk_retains_limb_count
set_option pp.all true in
#check @borrow_walk_conserves_full_subtraction_equation
#print axioms borrow_walk_conserves_full_subtraction_equation
set_option pp.all true in
#check @final_borrow_is_exact_input_underflow
#print axioms final_borrow_is_exact_input_underflow
end ShielddSecurity.TransferScalarBorrowWalk01
