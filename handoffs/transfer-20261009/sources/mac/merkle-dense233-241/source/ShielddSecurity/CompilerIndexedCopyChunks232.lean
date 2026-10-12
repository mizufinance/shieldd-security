import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedCopyChunks232
open CompilerIndexedCopyStream171
theorem check_append (p copy : Nat) (parent : Nat → Option Row) (fullLength : Nat)
 (indices later : List Nat) (rows rest : List Row) (count : indices.length=rows.length) :
 check p copy parent fullLength (indices++later) (rows++rest)=
 (check p copy parent fullLength indices rows && check p copy parent fullLength later rest) := by
 induction indices generalizing rows with
 | nil =>
   cases rows with
   | nil => rfl
   | cons row rows => simp only [List.length_nil,List.length_cons] at count; omega
 | cons position indices ih =>
   cases rows with
   | nil => simp only [List.length_nil,List.length_cons] at count; omega
   | cons row rows =>
     have smaller : indices.length=rows.length := Nat.succ.inj count
     simp only [List.cons_append,check,ih rows smaller,Bool.and_assoc]
end ShielddSecurity.CompilerIndexedCopyChunks232

set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyChunks232.check_append
#print axioms ShielddSecurity.CompilerIndexedCopyChunks232.check_append
