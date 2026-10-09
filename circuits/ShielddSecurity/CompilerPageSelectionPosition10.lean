import ShielddSecurity.CompilerPageSelection09
namespace ShielddSecurity.CompilerPageSelectionPosition10
open Compiler CompilerPageSelection09

theorem checked_append (get : Nat → Option Row) (firstRows secondRows : List Row) (firstIndices secondIndices : List Nat)
    (first : checkSelection get firstRows firstIndices=true) (second : checkSelection get secondRows secondIndices=true) :
    checkSelection get (firstRows++secondRows) (firstIndices++secondIndices)=true := by
  induction firstRows generalizing firstIndices with
  | nil =>
    cases firstIndices with
    | nil => exact second
    | cons index rest => simp [checkSelection] at first
  | cons row rows ih =>
    cases firstIndices with
    | nil => simp [checkSelection] at first
    | cons index indices =>
      simp only [checkSelection,Bool.and_eq_true] at first
      simp only [List.cons_append,checkSelection,Bool.and_eq_true]
      exact ⟨first.1,ih indices first.2⟩

theorem checked_position (get : Nat → Option Row) (rows : List Row) (indices : List Nat)
    (checked : checkSelection get rows indices=true) (position : Nat) (row : Row)
    (present : rows[position]?=some row) : ∃ index,indices[position]?=some index ∧ get index=some row := by
  induction rows generalizing indices position with
  | nil => simp at present
  | cons head tail ih =>
    cases indices with
    | nil => simp [checkSelection] at checked
    | cons index rest =>
      simp only [checkSelection,Bool.and_eq_true] at checked
      cases position with
      | zero =>
        have same : head=row := Option.some.inj present
        exact ⟨index,rfl,by simpa only [same] using of_decide_eq_true checked.1⟩
      | succ position =>
        exact ih rest checked.2 position (by simpa only [List.getElem?_cons_succ] using present)

theorem checked_index (get : Nat → Option Row) (rows : List Row) (indices : List Nat)
    (checked : checkSelection get rows indices=true) (position : Nat) (row : Row) (index : Nat)
    (present : rows[position]?=some row) (mapped : indices[position]?=some index) : get index=some row := by
  obtain ⟨other,found,result⟩ := checked_position get rows indices checked position row present
  have same : other=index := Option.some.inj (found.symm.trans mapped)
  simpa only [same] using result
end ShielddSecurity.CompilerPageSelectionPosition10
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelectionPosition10.checked_append
#print axioms ShielddSecurity.CompilerPageSelectionPosition10.checked_append
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelectionPosition10.checked_position
#print axioms ShielddSecurity.CompilerPageSelectionPosition10.checked_position
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelectionPosition10.checked_index
#print axioms ShielddSecurity.CompilerPageSelectionPosition10.checked_index
