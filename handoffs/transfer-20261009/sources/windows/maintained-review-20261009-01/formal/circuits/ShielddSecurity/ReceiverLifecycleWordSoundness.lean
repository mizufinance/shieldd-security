import ShielddSecurity.ScalarBooleanCanonical
import ShielddSecurity.ReceiverLifecycle
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 200000

namespace ShielddSecurity.ReceiverLifecycleWordSoundness

/-- Checked physical rows determine the complete Boolean word as well as its
bounded integer. Gate consumers can therefore use the same constrained bits. -/
theorem canonical_word {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (columns : List Nat) (value : Nat)
    (satisfied : Satisfies rho rows)
    (booleans : columns.all (fun column => Compiler.checkRow p rows (booleanRow column)) = true)
    (reconstruction : Compiler.checkRow p rows (reconstructionRow value columns) = true) :
    ∃ n : Nat, n < 2 ^ columns.length ∧ (n : F) = rho value ∧
      columns.map rho = (encodeBits columns.length n).map (fun bit => if bit then (1 : F) else 0) := by
  apply ScalarBooleanCanonical.columns_word rho columns value
  · intro row member
    obtain ⟨column,present,rfl⟩ := List.mem_map.mp member
    exact Compiler.checked_row_sound rho rows (booleanRow column) satisfied
      ((List.all_eq_true.mp booleans) column present)
  · exact Compiler.checked_row_sound rho rows (reconstructionRow value columns) satisfied reconstruction

/-- A symbolic recurrence splits a word without unrolling its bits. -/
theorem binary_append (prefixBits suffixBits : List Bool) :
    binary (prefixBits ++ suffixBits) = binary prefixBits + 2 ^ prefixBits.length * binary suffixBits := by
  induction prefixBits with
  | nil => simp [binary]
  | cons bit bits ih =>
      simp only [List.cons_append,binary,ih,List.length_cons,Nat.pow_succ]
      ring

private theorem binary_false (width : Nat) : binary (List.replicate width false) = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ,binary,ih]

/-- The three status bits and zero high suffix imply the native active-status
predicate. Physical gate composition must supply this Boolean word shape. -/
theorem active_word (middle : List Bool) (width : middle.length = 64) :
    ReceiverLifecycle.LegalActive (binary ([true,false,false] ++ middle ++ List.replicate 64 false)) := by
  have word : binary ([true,false,false] ++ middle ++ List.replicate 64 false) = 1 + 8 * binary middle := by
    rw [binary_append,binary_append,binary_false]
    simp [binary]
  have bounded := binary_bound middle
  rw [width] at bounded
  unfold ReceiverLifecycle.LegalActive
  rw [word]
  constructor
  · omega
  · norm_num at bounded ⊢
    omega

set_option pp.all true in
#check @canonical_word
#print axioms canonical_word
set_option pp.all true in
#check @binary_append
#print axioms binary_append
set_option pp.all true in
#check @active_word
#print axioms active_word

end ShielddSecurity.ReceiverLifecycleWordSoundness
