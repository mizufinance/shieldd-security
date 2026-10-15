import ShielddSecurity.TransferScalarWordPrimitives01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCarrySchedule01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords mac128 split128)
/-! Symbolic carry-chain conservation for the pinned scalar MAC schedule.
Each pair supplies the current accumulator limb and modulus limb. The exact
128-bit MAC feeds its carry into the next limb; the final carry is retained.
Dropping the low output limb and appending that carry gives integer division
by radix64. This closes the arithmetic schedule equation for arbitrary finite
vectors, without asserting Rust trace correspondence, ADC/SBB or byte layout. -/
def macLoop (multiplier carry : UInt64) : List (UInt64 × UInt64) → List UInt64 × UInt64
  | [] => ([], carry)
  | pair :: rest =>
    let step := split128 (mac128 pair.1 multiplier pair.2 carry)
    let after := macLoop multiplier step.2 rest
    (step.1 :: after.1, after.2)

def dropLowAndAppendCarry (output : List UInt64 × UInt64) : List UInt64 :=
  output.1.drop 1 ++ [output.2]

theorem packing_append_preserves_positional_value (left right : List UInt64) :
    packWords (left ++ right) = packWords left + radix64 ^ left.length * packWords right := by
  induction left with
  | nil => simp only [List.nil_append, packWords, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons word rest ih =>
    change word.toNat + radix64 * packWords (rest ++ right) =
      (word.toNat + radix64 * packWords rest) + radix64 ^ (rest.length + 1) * packWords right
    rw [ih, Nat.pow_succ, Nat.mul_add]
    ac_rfl

theorem carry_walk_retains_limb_count (multiplier carry : UInt64) (pairs : List (UInt64 × UInt64)) :
    (macLoop multiplier carry pairs).1.length = pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest ih =>
    change (macLoop multiplier (split128 (mac128 pair.1 multiplier pair.2 carry)).2 rest).1.length + 1 = rest.length + 1
    rw [ih]

theorem carry_walk_conserves_full_integer (multiplier carry : UInt64) (pairs : List (UInt64 × UInt64)) :
    packWords (macLoop multiplier carry pairs).1 + radix64 ^ pairs.length * (macLoop multiplier carry pairs).2.toNat =
      packWords (pairs.map Prod.fst) + multiplier.toNat * packWords (pairs.map Prod.snd) + carry.toNat := by
  induction pairs generalizing carry with
  | nil => simp only [macLoop, packWords, List.map_nil, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.mul_zero, Nat.zero_add]
  | cons pair rest ih =>
    let step := split128 (mac128 pair.1 multiplier pair.2 carry)
    let after := macLoop multiplier step.2 rest
    have tail := ih step.2
    have first := TransferScalarWordPrimitives01.widened_u64_mac_low_word_and_carry_conserve_value pair.1 multiplier pair.2 carry
    change step.1.toNat + radix64 * packWords after.1 + radix64 ^ (rest.length + 1) * after.2.toNat =
      pair.1.toNat + radix64 * packWords (rest.map Prod.fst) +
        multiplier.toNat * (pair.2.toNat + radix64 * packWords (rest.map Prod.snd)) + carry.toNat
    calc
      _ = step.1.toNat + radix64 * (packWords after.1 + radix64 ^ rest.length * after.2.toNat) := by
        rw [Nat.pow_succ, Nat.mul_add]
        ac_rfl
      _ = step.1.toNat + radix64 * (packWords (rest.map Prod.fst) + multiplier.toNat * packWords (rest.map Prod.snd) + step.2.toNat) := by
        rw [tail]
      _ = (step.1.toNat + radix64 * step.2.toNat) + radix64 * packWords (rest.map Prod.fst) + multiplier.toNat * (radix64 * packWords (rest.map Prod.snd)) := by
        rw [Nat.mul_add, Nat.mul_add]
        ac_rfl
      _ = (pair.1.toNat + multiplier.toNat * pair.2.toNat + carry.toNat) + radix64 * packWords (rest.map Prod.fst) + multiplier.toNat * (radix64 * packWords (rest.map Prod.snd)) := by
        rw [first]
      _ = _ := by
        rw [Nat.mul_add]
        ac_rfl

theorem dropping_low_limb_and_appending_carry_is_radix_quotient
    (low carry : UInt64) (rest : List UInt64) :
    packWords (rest ++ [carry]) =
      (packWords (low :: rest) + radix64 ^ (rest.length + 1) * carry.toNat) / radix64 := by
  rw [packing_append_preserves_positional_value]
  change packWords rest + radix64 ^ rest.length * carry.toNat =
    (low.toNat + radix64 * packWords rest + radix64 ^ (rest.length + 1) * carry.toNat) / radix64
  symm
  calc
    _ = (low.toNat + radix64 * (packWords rest + radix64 ^ rest.length * carry.toNat)) / radix64 := by
      congr 1
      rw [Nat.pow_succ, Nat.mul_add]
      ac_rfl
    _ = low.toNat / radix64 + (packWords rest + radix64 ^ rest.length * carry.toNat) := Nat.add_mul_div_left _ _ (by decide)
    _ = _ := by
      have lowBound : low.toNat < radix64 := low.toNat_lt
      rw [Nat.div_eq_of_lt lowBound, Nat.zero_add]

theorem nonempty_mac_walk_drops_to_exact_quotient
    (multiplier carry : UInt64) (pairs : List (UInt64 × UInt64)) (nonempty : pairs ≠ []) :
    packWords (dropLowAndAppendCarry (macLoop multiplier carry pairs)) =
      (packWords (pairs.map Prod.fst) + multiplier.toNat * packWords (pairs.map Prod.snd) + carry.toNat) / radix64 := by
  have conserved := carry_walk_conserves_full_integer multiplier carry pairs
  have length := carry_walk_retains_limb_count multiplier carry pairs
  cases output : (macLoop multiplier carry pairs).1 with
  | nil =>
    rw [output, List.length_nil] at length
    exact False.elim (nonempty (List.eq_nil_of_length_eq_zero length.symm))
  | cons low rest =>
    change packWords ((macLoop multiplier carry pairs).1.drop 1 ++ [(macLoop multiplier carry pairs).2]) = _
    rw [output]
    change packWords (rest ++ [(macLoop multiplier carry pairs).2]) = _
    rw [output] at conserved length
    rw [← conserved, ← length]
    exact dropping_low_limb_and_appending_carry_is_radix_quotient low _ rest

set_option pp.all true in
#check @macLoop
#print axioms macLoop
set_option pp.all true in
#check @dropLowAndAppendCarry
#print axioms dropLowAndAppendCarry
set_option pp.all true in
#check @packing_append_preserves_positional_value
#print axioms packing_append_preserves_positional_value
set_option pp.all true in
#check @carry_walk_retains_limb_count
#print axioms carry_walk_retains_limb_count
set_option pp.all true in
#check @carry_walk_conserves_full_integer
#print axioms carry_walk_conserves_full_integer
set_option pp.all true in
#check @dropping_low_limb_and_appending_carry_is_radix_quotient
#print axioms dropping_low_limb_and_appending_carry_is_radix_quotient
set_option pp.all true in
#check @nonempty_mac_walk_drops_to_exact_quotient
#print axioms nonempty_mac_walk_drops_to_exact_quotient
end ShielddSecurity.TransferScalarCarrySchedule01
