import ShielddSecurity.TransferScalarChoiceBit01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideProduct01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop dropLowAndAppendCarry)
/-! Symbolic four-word schoolbook rows match source16 MAC call shape:
right/self selects each row multiplier, left/rhs supplies column words.
Retain one low word per row and carry into next four-word accumulator.
Full eight-limb integer product and range are derived without unrolled
wide constraint walks. Native primitive/compiler/source execution and final
wide Montgomery reduction remain explicit; no native/certification credit. -/

def multiplyWalk (left : List UInt64) : List UInt64 → List UInt64 → List UInt64
  | [], accumulated => accumulated
  | multiplier :: rest, accumulated =>
    let output := macLoop multiplier 0 (accumulated.zip left)
    output.1.headD 0 :: multiplyWalk left rest (dropLowAndAppendCarry output)

def sourceWideProduct (self rhs : Vector UInt64 4) : List UInt64 :=
  multiplyWalk rhs.toList self.toList (List.replicate 4 0)

theorem retained_low_word_and_shifted_carry_preserve_full_output
    (output : List UInt64 × UInt64) (nonempty : output.1 ≠ []) :
    (output.1.headD 0).toNat + radix64 * packWords (dropLowAndAppendCarry output) =
      packWords output.1 + radix64 ^ output.1.length * output.2.toNat := by
  cases output with
  | mk words carry =>
    cases words with
    | nil => exact False.elim (nonempty rfl)
    | cons low rest =>
      change low.toNat + radix64 * packWords (rest ++ [carry]) =
        low.toNat + radix64 * packWords rest + radix64 ^ (rest.length + 1) * carry.toNat
      rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value]
      change low.toNat + radix64 * (packWords rest + radix64 ^ rest.length * carry.toNat) = _
      rw [Nat.pow_succ, Nat.mul_add]
      ac_rfl

theorem four_word_mac_row_preserves_next_accumulator_width
    (multiplier : UInt64) (left accumulated : List UInt64)
    (leftWidth : left.length = 4) (accumulatedWidth : accumulated.length = 4) :
    (dropLowAndAppendCarry (macLoop multiplier 0 (accumulated.zip left))).length = 4 := by
  have length := TransferScalarCarrySchedule01.carry_walk_retains_limb_count multiplier 0 (accumulated.zip left)
  rw [List.length_zip, leftWidth, accumulatedWidth, Nat.min_self] at length
  change ((macLoop multiplier 0 (accumulated.zip left)).1.drop 1 ++
    [(macLoop multiplier 0 (accumulated.zip left)).2]).length = 4
  rw [List.length_append, List.length_drop, length]
  rfl

theorem finite_mac_row_derives_exact_accumulation_equation
    (multiplier : UInt64) (left accumulated : List UInt64)
    (leftWidth : left.length = 4) (accumulatedWidth : accumulated.length = 4) :
    ((macLoop multiplier 0 (accumulated.zip left)).1.headD 0).toNat +
      radix64 * packWords (dropLowAndAppendCarry (macLoop multiplier 0 (accumulated.zip left))) =
      packWords accumulated + multiplier.toNat * packWords left := by
  have equalWidths : accumulated.length = left.length := accumulatedWidth.trans leftWidth.symm
  have length := TransferScalarCarrySchedule01.carry_walk_retains_limb_count multiplier 0 (accumulated.zip left)
  rw [List.length_zip, leftWidth, accumulatedWidth, Nat.min_self] at length
  have nonempty : (macLoop multiplier 0 (accumulated.zip left)).1 ≠ [] := by
    intro empty
    rw [empty, List.length_nil] at length
    omega
  have retained := retained_low_word_and_shifted_carry_preserve_full_output (macLoop multiplier 0 (accumulated.zip left)) nonempty
  rw [length] at retained
  have conserved := TransferScalarCarrySchedule01.carry_walk_conserves_full_integer multiplier 0 (accumulated.zip left)
  rw [List.length_zip, leftWidth, accumulatedWidth, Nat.min_self,
    List.map_fst_zip (Nat.le_of_eq equalWidths), List.map_snd_zip (Nat.le_of_eq equalWidths.symm)] at conserved
  exact retained.trans conserved

theorem symbolic_schoolbook_walk_derives_width_and_exact_full_product
    (left right accumulated : List UInt64) (leftWidth : left.length = 4) (accumulatedWidth : accumulated.length = 4) :
    (multiplyWalk left right accumulated).length = 4 + right.length ∧
      packWords (multiplyWalk left right accumulated) = packWords accumulated + packWords right * packWords left := by
  induction right generalizing accumulated with
  | nil =>
    exact ⟨accumulatedWidth, by simp only [multiplyWalk, packWords, Nat.zero_mul, Nat.add_zero]⟩
  | cons multiplier rest ih =>
    let output := macLoop multiplier 0 (accumulated.zip left)
    have nextWidth := four_word_mac_row_preserves_next_accumulator_width multiplier left accumulated leftWidth accumulatedWidth
    have tail := ih (dropLowAndAppendCarry output) nextWidth
    have row := finite_mac_row_derives_exact_accumulation_equation multiplier left accumulated leftWidth accumulatedWidth
    constructor
    · change (multiplyWalk left rest (dropLowAndAppendCarry output)).length + 1 = 4 + (rest.length + 1)
      rw [tail.1]
      omega
    · change (output.1.headD 0).toNat + radix64 * packWords (multiplyWalk left rest (dropLowAndAppendCarry output)) =
        packWords accumulated + (multiplier.toNat + radix64 * packWords rest) * packWords left
      rw [tail.2, Nat.mul_add]
      calc
        _ = ((output.1.headD 0).toNat + radix64 * packWords (dropLowAndAppendCarry output)) +
            radix64 * (packWords rest * packWords left) := by ac_rfl
        _ = (packWords accumulated + multiplier.toNat * packWords left) +
            radix64 * (packWords rest * packWords left) := by rw [row]
        _ = _ := by rw [Nat.add_mul]; ac_rfl

theorem source_schoolbook_product_has_exact_eight_limbs_value_and_range (self rhs : Vector UInt64 4) :
    (sourceWideProduct self rhs).length = 8 ∧
      packWords (sourceWideProduct self rhs) = packWords self.toList * packWords rhs.toList ∧
      packWords (sourceWideProduct self rhs) < radix64 ^ 8 := by
  have full := symbolic_schoolbook_walk_derives_width_and_exact_full_product rhs.toList self.toList
    (List.replicate 4 0) Vector.length_toList (by decide)
  have width : (sourceWideProduct self rhs).length = 8 := by simpa only [sourceWideProduct, Vector.length_toList] using full.1
  have zero : packWords (List.replicate 4 (0 : UInt64)) = 0 := by decide
  have value : packWords (sourceWideProduct self rhs) = packWords self.toList * packWords rhs.toList := by
    simpa only [sourceWideProduct, zero, Nat.zero_add] using full.2
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceWideProduct self rhs)
  rw [width] at bounded
  exact ⟨width, value, bounded⟩

set_option pp.all true in
#check @multiplyWalk
#print axioms multiplyWalk
set_option pp.all true in
#check @sourceWideProduct
#print axioms sourceWideProduct
set_option pp.all true in
#check @retained_low_word_and_shifted_carry_preserve_full_output
#print axioms retained_low_word_and_shifted_carry_preserve_full_output
set_option pp.all true in
#check @four_word_mac_row_preserves_next_accumulator_width
#print axioms four_word_mac_row_preserves_next_accumulator_width
set_option pp.all true in
#check @finite_mac_row_derives_exact_accumulation_equation
#print axioms finite_mac_row_derives_exact_accumulation_equation
set_option pp.all true in
#check @symbolic_schoolbook_walk_derives_width_and_exact_full_product
#print axioms symbolic_schoolbook_walk_derives_width_and_exact_full_product
set_option pp.all true in
#check @source_schoolbook_product_has_exact_eight_limbs_value_and_range
#print axioms source_schoolbook_product_has_exact_eight_limbs_value_and_range
end ShielddSecurity.TransferScalarWideProduct01
