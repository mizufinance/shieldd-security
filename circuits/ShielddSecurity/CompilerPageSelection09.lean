import ShielddSecurity.Compiler
namespace ShielddSecurity.CompilerPageSelection09
open Compiler

def lookup (pageSize : Nat) (pages : List (List Row)) (index : Nat) : Option Row :=
  (pages[index/pageSize]?).bind (fun page => page[index%pageSize]?)

theorem lookup_mem (pageSize : Nat) (pages : List (List Row)) (index : Nat) (row : Row)
    (found : lookup pageSize pages index=some row) : row∈pages.flatten := by
  cases selected : pages[index/pageSize]? with
  | none => simp [lookup,selected] at found
  | some page =>
    have present : page[index%pageSize]?=some row := by simpa only [lookup,selected,Option.bind_some] using found
    exact List.mem_flatten.mpr ⟨page,List.mem_of_getElem? selected,List.mem_of_getElem? present⟩

def checkSelection (get : Nat → Option Row) : List Row → List Nat → Bool
  | [],[] => true
  | row::rows,index::indices => decide (get index=some row) && checkSelection get rows indices
  | _,_ => false

theorem checked_selection (get : Nat → Option Row) (rows : List Row) (indices : List Nat)
    (checked : checkSelection get rows indices=true) :
    ∀ row∈rows,∃ index∈indices,get index=some row := by
  induction rows generalizing indices with
  | nil => simp
  | cons head tail ih =>
    cases indices with
    | nil => simp [checkSelection] at checked
    | cons index rest =>
      simp only [checkSelection,Bool.and_eq_true] at checked
      intro row member
      rcases List.mem_cons.mp member with rfl|member
      · exact ⟨index,by simp,of_decide_eq_true checked.1⟩
      · obtain ⟨i,present,found⟩ := ih rest checked.2 row member
        exact ⟨i,List.mem_cons_of_mem index present,found⟩

theorem checked_inclusion (get : Nat → Option Row) (rows : List Row) (indices : List Nat)
    (full : List Row) (checked : checkSelection get rows indices=true)
    (membership : ∀ index row,get index=some row → row∈full) : ∀ row∈rows,row∈full := by
  intro row member
  obtain ⟨index,_,found⟩ := checked_selection get rows indices checked row member
  exact membership index row found

def checkOutside (low high : Nat) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a++row.b).all (fun term => decide (term.1<low ∨ high≤term.1)))

theorem checked_outside (low high : Nat) (rows : List Row) (checked : checkOutside low high rows=true) :
    ∀ row∈rows,∀ term∈row.a++row.b,term.1<low ∨ high≤term.1 := by
  intro row member term present
  have accepted := List.all_eq_true.mp checked row member
  exact of_decide_eq_true (List.all_eq_true.mp accepted term present)
end ShielddSecurity.CompilerPageSelection09
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelection09.lookup_mem
#print axioms ShielddSecurity.CompilerPageSelection09.lookup_mem
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelection09.checked_selection
#print axioms ShielddSecurity.CompilerPageSelection09.checked_selection
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelection09.checked_inclusion
#print axioms ShielddSecurity.CompilerPageSelection09.checked_inclusion
set_option pp.all true in
#check @ShielddSecurity.CompilerPageSelection09.checked_outside
#print axioms ShielddSecurity.CompilerPageSelection09.checked_outside
