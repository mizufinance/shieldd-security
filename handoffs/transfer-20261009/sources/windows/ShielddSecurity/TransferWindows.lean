import Mathlib.Algebra.Group.Basic
import ShielddSecurity.Range

set_option maxHeartbeats 100000

namespace ShielddSecurity.TransferWindows

/-- Little-endian radix-four digits. Digit bounds and bit reconstruction are
separate circuit obligations; this recurrence does not assume them. -/
def digitsValue : List Nat → Nat
  | [] => 0
  | d :: ds => d + 4 * digitsValue ds

/-- Pair the scalar's existing little-endian Boolean bits. An odd final bit
gets the runtime's default false high bit; Transfer IVK has even width252. -/
def pairDigits : List Bool → List Nat
  | [] => []
  | [low] => [if low then 1 else 0]
  | low :: high :: rest =>
      ((if low then 1 else 0) + 2 * (if high then 1 else 0)) :: pairDigits rest

theorem pair_digits_value (bits : List Bool) :
    digitsValue (pairDigits bits) = ShielddSecurity.binary bits := by
  match bits with
  | [] => rfl
  | [low] => cases low <;> rfl
  | low :: high :: rest =>
    simp only [pairDigits, digitsValue, ShielddSecurity.binary]
    rw [pair_digits_value rest]
    omega
termination_by structural bits

/-- The runtime variable-base loop visits reversed two-bit chunks. Its
mathematical group interpretation uses the same least-significant-first list. -/
def variableValue {G : Type} [AddCommGroup G] (base : G) : List Nat → G
  | [] => 0
  | d :: ds => 4 • variableValue base ds + d • base

/-- Exact reversed iterator order of the circuit's variable-base loop. -/
theorem variable_loop {G : Type} [AddCommGroup G] (base : G) (ds : List Nat) :
    ds.reverse.foldl (fun acc d => 4 • acc + d • base) 0 = variableValue base ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih, variableValue]

theorem variable_value {G : Type} [AddCommGroup G] (base : G) (ds : List Nat) :
    variableValue base ds = digitsValue ds • base := by
  induction ds with
  | nil => simp [variableValue, digitsValue]
  | cons d ds ih =>
    simp [variableValue, digitsValue, ih, add_nsmul, mul_nsmul, add_comm]
    rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

/-- The fixed-base loop visits ascending chunks while advancing its base by
four. This is a symbolic recurrence, not an affine-row soundness claim. -/
def fixedValue {G : Type} [AddCommGroup G] : G → G → List Nat → G
  | acc, _, [] => acc
  | acc, base, d :: ds => fixedValue (acc + d • base) (4 • base) ds

theorem fixed_value {G : Type} [AddCommGroup G] (ds : List Nat) (acc base : G) :
    fixedValue acc base ds = acc + digitsValue ds • base := by
  induction ds generalizing acc base with
  | nil => simp [fixedValue, digitsValue]
  | cons d ds ih =>
    simp only [fixedValue, ih, digitsValue, add_nsmul, mul_nsmul]
    simp only [← add_assoc]

set_option pp.all true in
#check @pair_digits_value
#print axioms pair_digits_value
set_option pp.all true in
#check @variable_loop
#print axioms variable_loop
set_option pp.all true in
#check @variable_value
#print axioms variable_value
set_option pp.all true in
#check @fixed_value
#print axioms fixed_value

end ShielddSecurity.TransferWindows
