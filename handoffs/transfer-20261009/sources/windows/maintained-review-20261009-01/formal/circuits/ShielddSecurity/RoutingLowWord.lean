import ShielddSecurity.ScalarBits

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.RoutingLowWord

/-- Splitting little-endian bits separates the two integer places exactly. -/
theorem binary_append (first second : List Bool) :
    binary (first ++ second) = binary first + 2^first.length * binary second := by
  induction first with
  | nil => simp [binary]
  | cons flag tail ih =>
      cases flag <;> simp only [List.cons_append,binary,ih,List.length_cons,
        Bool.false_eq_true,ite_false,ite_true,Nat.pow_succ] <;> ring

/-- A prefix of a canonical decomposition is the integer residue, with its
bound derived from the bits rather than supplied as a desired word premise. -/
theorem take_mod (bits : List Bool) (width : Nat) (inside : width ≤ bits.length) :
    binary (bits.take width) = binary bits % 2^width := by
  have length : (bits.take width).length = width := by
    simp only [List.length_take,Nat.min_eq_left inside]
  have bound : binary (bits.take width) < 2^width := by
    simpa only [length] using binary_bound (bits.take width)
  have split := binary_append (bits.take width) (bits.drop width)
  rw [List.take_append_drop,length] at split
  rw [split]
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.add_zero,
    Nat.mod_mod,Nat.zero_mod,Nat.mod_eq_of_lt bound]

theorem low32 (bits : List Bool) (length : bits.length = 255) (native : Nat)
    (canonical : binary bits = native) :
    binary (bits.take 32) = native % 2^32 ∧ binary (bits.take 32) < 2^32 := by
  have inside : 32 ≤ bits.length := by omega
  refine ⟨?_,?_⟩
  · rw [take_mod bits 32 inside,canonical]
  · have takeLength : (bits.take 32).length = 32 := by
      simp only [List.length_take,Nat.min_eq_left inside]
    simpa only [takeLength] using binary_bound (bits.take 32)

theorem low_bit (head : Bool) (tail : List Bool) :
    binary (head :: tail) % 2 = if head then 1 else 0 := by
  have initial := take_mod (head :: tail) 1 (by simp)
  simpa only [List.take_succ_cons,List.take_zero,binary,Nat.mul_zero,Nat.add_zero,
    Nat.pow_one] using initial.symm

set_option pp.all true in
#check @binary_append
#print axioms binary_append
set_option pp.all true in
#check @take_mod
#print axioms take_mod
set_option pp.all true in
#check @low32
#print axioms low32
set_option pp.all true in
#check @low_bit
#print axioms low_bit

end ShielddSecurity.RoutingLowWord
