import ShielddSecurity.TransferScalarInputFamily01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSquareCross01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop)
/-! The square prefix uses shrinking MAC rows of lengths3,2,1. Each row
retains its first two words and passes the remaining words plus exact carry
to the next row. Symbolic conservation derives all six cross terms without
unrolling wide constraints. Doubling shifts, diagonal terms, final reduction
and native source/compiler/caller correspondence are separate obligations. -/

def crossValue : List UInt64 → Nat
  | [] => 0
  | first :: rest => first.toNat * packWords rest + radix64 ^ 2 * crossValue rest

def crossWalk : List UInt64 → List UInt64 → List UInt64
  | [], accumulated => accumulated
  | [_], accumulated => accumulated
  | multiplier :: next :: rest, accumulated =>
    let output := macLoop multiplier 0 (accumulated.zip (next :: rest))
    let full := output.1 ++ [output.2]
    full.take 2 ++ crossWalk (next :: rest) (full.drop 2)

def sourceCrossWords (self : Vector UInt64 4) : List UInt64 :=
  0 :: crossWalk self.toList (List.replicate 3 0)

theorem mac_row_appended_carry_derives_exact_width_and_integer_value
    (multiplier : UInt64) (accumulated right : List UInt64) (width : accumulated.length = right.length) :
    ((macLoop multiplier 0 (accumulated.zip right)).1 ++ [(macLoop multiplier 0 (accumulated.zip right)).2]).length = right.length + 1 ∧
      packWords ((macLoop multiplier 0 (accumulated.zip right)).1 ++ [(macLoop multiplier 0 (accumulated.zip right)).2]) =
        packWords accumulated + multiplier.toNat * packWords right := by
  let output := macLoop multiplier 0 (accumulated.zip right)
  have pairsWidth : (accumulated.zip right).length = right.length := by
    rw [List.length_zip, width, Nat.min_self]
  have outputWidth : output.1.length = right.length := by
    rw [TransferScalarCarrySchedule01.carry_walk_retains_limb_count, pairsWidth]
  have conserved := TransferScalarCarrySchedule01.carry_walk_conserves_full_integer multiplier 0 (accumulated.zip right)
  rw [List.map_fst_zip (Nat.le_of_eq width), List.map_snd_zip (Nat.le_of_eq width.symm),
    pairsWidth, UInt64.toNat_zero, Nat.add_zero] at conserved
  change (output.1 ++ [output.2]).length = right.length + 1 ∧
    packWords (output.1 ++ [output.2]) = packWords accumulated + multiplier.toNat * packWords right
  constructor
  · rw [List.length_append, outputWidth, List.length_singleton]
  · rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value, outputWidth]
    change packWords output.1 + radix64 ^ right.length * output.2.toNat = _
    exact conserved

theorem symbolic_shrinking_cross_walk_derives_width_and_exact_cross_value
    (words accumulated : List UInt64) (width : accumulated.length = words.length - 1) :
    (crossWalk words accumulated).length = 2 * (words.length - 1) ∧
      packWords (crossWalk words accumulated) = packWords accumulated + crossValue words := by
  induction words generalizing accumulated with
  | nil =>
    have empty : accumulated = [] := List.eq_nil_of_length_eq_zero width
    subst accumulated
    exact ⟨rfl, rfl⟩
  | cons multiplier rest ih =>
    cases rest with
    | nil =>
      have empty : accumulated = [] := List.eq_nil_of_length_eq_zero width
      subst accumulated
      simp only [crossWalk, crossValue, packWords, List.length_nil, List.length_cons,
        Nat.mul_zero, Nat.add_zero]
    | cons next rest =>
      let output := macLoop multiplier 0 (accumulated.zip (next :: rest))
      let full := output.1 ++ [output.2]
      have inputWidth : accumulated.length = (next :: rest).length := by
        simp only [List.length_cons] at width ⊢
        omega
      have row := mac_row_appended_carry_derives_exact_width_and_integer_value multiplier accumulated (next :: rest) inputWidth
      change full.length = rest.length + 2 ∧ packWords full = packWords accumulated + multiplier.toNat * packWords (next :: rest) at row
      have dropWidth : (full.drop 2).length = (next :: rest).length - 1 := by
        rw [List.length_drop, row.1, List.length_cons]
        omega
      have tail := ih (full.drop 2) dropWidth
      have takeWidth : (full.take 2).length = 2 := by
        rw [List.length_take, row.1, Nat.min_eq_left (by omega : 2 ≤ rest.length + 2)]
      have split := TransferScalarCarrySchedule01.packing_append_preserves_positional_value (full.take 2) (full.drop 2)
      rw [List.take_append_drop, takeWidth] at split
      change (full.take 2 ++ crossWalk (next :: rest) (full.drop 2)).length = 2 * ((multiplier :: next :: rest).length - 1) ∧
        packWords (full.take 2 ++ crossWalk (next :: rest) (full.drop 2)) = packWords accumulated + crossValue (multiplier :: next :: rest)
      constructor
      · rw [List.length_append, takeWidth, tail.1]
        simp only [List.length_cons]
        omega
      · rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value, takeWidth, tail.2, Nat.mul_add]
        calc
          _ = (packWords (full.take 2) + radix64 ^ 2 * packWords (full.drop 2)) + radix64 ^ 2 * crossValue (next :: rest) := by ac_rfl
          _ = (packWords accumulated + multiplier.toNat * packWords (next :: rest)) + radix64 ^ 2 * crossValue (next :: rest) := by rw [← split, row.2]
          _ = _ := by rw [crossValue]; ac_rfl

theorem source_six_cross_mac_prefix_derives_seven_words_and_exact_cross_integer (self : Vector UInt64 4) :
    (sourceCrossWords self).length = 7 ∧ packWords (sourceCrossWords self) = radix64 * crossValue self.toList := by
  have initialWidth : (List.replicate 3 (0 : UInt64)).length = self.toList.length - 1 := by
    rw [List.length_replicate, Vector.length_toList]
  have contract := symbolic_shrinking_cross_walk_derives_width_and_exact_cross_value self.toList (List.replicate 3 0) initialWidth
  rw [Vector.length_toList] at contract
  have zero : packWords (List.replicate 3 (0 : UInt64)) = 0 := rfl
  rw [zero, Nat.zero_add] at contract
  change (crossWalk self.toList (List.replicate 3 0)).length + 1 = 7 ∧
    0 + radix64 * packWords (crossWalk self.toList (List.replicate 3 0)) = radix64 * crossValue self.toList
  rw [contract.1, contract.2, Nat.zero_add]

set_option pp.all true in
#check @crossValue
#print axioms crossValue
set_option pp.all true in
#check @crossWalk
#print axioms crossWalk
set_option pp.all true in
#check @sourceCrossWords
#print axioms sourceCrossWords
set_option pp.all true in
#check @mac_row_appended_carry_derives_exact_width_and_integer_value
#print axioms mac_row_appended_carry_derives_exact_width_and_integer_value
set_option pp.all true in
#check @symbolic_shrinking_cross_walk_derives_width_and_exact_cross_value
#print axioms symbolic_shrinking_cross_walk_derives_width_and_exact_cross_value
set_option pp.all true in
#check @source_six_cross_mac_prefix_derives_seven_words_and_exact_cross_integer
#print axioms source_six_cross_mac_prefix_derives_seven_words_and_exact_cross_integer
end ShielddSecurity.TransferScalarSquareCross01
