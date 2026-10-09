import ShielddSecurity.GroupFixedCircuitCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupCircuitProgramTrace

open GroupFixedCircuitCompletion

theorem output_append (input : Linear × Linear) (left right : List Program) :
    output input (left ++ right) = output (output input left) right := by
  induction left generalizing input with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.cons_append, output] using ih head.output

theorem aligned_append (input : Linear × Linear) (left right : List Program) :
    Aligned input (left ++ right) ↔
      Aligned input left ∧ Aligned (output input left) right := by
  induction left generalizing input with
  | nil => simp only [List.nil_append, Aligned, output, true_and]
  | cons head tail ih =>
      change (head.input = input ∧ Aligned head.output (tail ++ right)) ↔
        (head.input = input ∧ Aligned head.output tail) ∧
          Aligned (output head.output tail) right
      rw [ih]
      exact and_assoc.symm

theorem rows_append (left right : List Program) :
    rows (left ++ right) = rows left ++ rows right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, rows, ih, List.append_assoc]

theorem run_append {F : Type} [Field F] (base : Nat → F) (left right : List Program) :
    run base (left ++ right) = run (run base left) right := by
  induction left generalizing base with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.cons_append, run] using ih (head.build base)

set_option pp.all true in
#check @output_append
#print axioms output_append
set_option pp.all true in
#check @aligned_append
#print axioms aligned_append
set_option pp.all true in
#check @rows_append
#print axioms rows_append
set_option pp.all true in
#check @run_append
#print axioms run_append

end ShielddSecurity.GroupCircuitProgramTrace
