import ShielddSecurity.CompilerIndexed01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedCoverage36
open Compiler CompilerIndexed01
theorem every_position (p : Nat) (original expected : Array Row) (mapping : Array Nat)
    (checked : checkOriginalCoverage p 0 original expected mapping=true) (index : Nat) (bound : index<original.size) :
    checkOriginalAt p 0 original expected mapping index=true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 index (List.mem_range.mpr bound)
theorem append_coverage (p : Nat) (headRows : List Row) (actual expected : Row)
    (left : canonical p actual.a=canonical p expected.a) (right : canonical p actual.b=canonical p expected.b) :
    checkOriginalCoverage p 0 (headRows++[actual]).toArray (headRows++[expected]).toArray (List.range (headRows.length+1)).toArray=true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · simp [List.size_toArray]
  · apply List.all_eq_true.mpr
    intro index member
    have bound : index<headRows.length+1 := by simpa only [List.size_toArray,List.length_append,List.length_singleton] using List.mem_range.mp member
    have mapped : (List.range (headRows.length+1)).toArray[index]?=some index := by
      simpa only [List.getElem?_toArray] using List.getElem?_range bound
    by_cases before : index<headRows.length
    · have present : headRows[index]?=some headRows[index] := List.getElem?_eq_getElem before
      simp only [checkOriginalAt,List.getElem?_toArray,List.getElem?_append_left before,present,mapped,unoutline_zero,checkRowAt]
      simp
    · have equal : index=headRows.length := by omega
      subst index
      simp [checkOriginalAt,checkRowAt,unoutline_zero,left,right]
theorem reject_position (p : Nat) (original expected : Array Row) (mapping : Array Nat) (index : Nat)
    (bound : index<original.size) (rejected : checkOriginalAt p 0 original expected mapping index=false) :
    checkOriginalCoverage p 0 original expected mapping=false := by
  cases checked : checkOriginalCoverage p 0 original expected mapping with
  | false => rfl
  | true =>
    have accepted := every_position p original expected mapping checked index bound
    rw [rejected] at accepted
    contradiction
end ShielddSecurity.CompilerIndexedCoverage36

set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCoverage36.every_position
#print axioms ShielddSecurity.CompilerIndexedCoverage36.every_position
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCoverage36.append_coverage
#print axioms ShielddSecurity.CompilerIndexedCoverage36.append_coverage
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCoverage36.reject_position
#print axioms ShielddSecurity.CompilerIndexedCoverage36.reject_position
