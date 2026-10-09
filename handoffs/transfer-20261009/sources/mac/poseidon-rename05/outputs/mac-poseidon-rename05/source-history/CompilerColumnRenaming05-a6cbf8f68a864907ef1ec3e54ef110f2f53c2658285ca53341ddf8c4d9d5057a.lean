import ShielddSecurity.CompilerCompletion
namespace ShielddSecurity.CompilerColumnRenaming05
open Compiler CompilerCompletion

def linear (rename : Nat → Nat) (terms : Linear) : Linear :=
  terms.map (fun term => (rename term.1,term.2))
def row (rename : Nat → Nat) (value : Row) : Row := ⟨linear rename value.a,linear rename value.b⟩
def rows (rename : Nat → Nat) (values : List Row) : List Row := values.map (row rename)
def step (rename : Nat → Nat) : Step → Step
  | .square input remainder output => .square (linear rename input) (linear rename remainder) (rename output)
  | .product left right remainder output auxiliary => .product (linear rename left) (linear rename right) (linear rename remainder) (rename output) (rename auxiliary)
  | .equal left right => .equal (linear rename left) (linear rename right)
  | .squareEqual input target => .squareEqual (linear rename input) (linear rename target)
def steps (rename : Nat → Nat) (values : List Step) : List Step := values.map (step rename)

variable {F : Type} [Field F]
theorem eval_linear (rename : Nat → Nat) (rho : Nat → F) (terms : Linear) :
    eval rho (linear rename terms)=eval (fun column => rho (rename column)) terms := by
  induction terms with
  | nil => rfl
  | cons head tail ih => simp only [linear,List.map_cons,eval,ih]

theorem satisfies_rows (rename : Nat → Nat) (rho : Nat → F) (values : List Row) :
    Satisfies rho (rows rename values) ↔ Satisfies (fun column => rho (rename column)) values := by
  constructor
  · intro satisfied value member
    have result := satisfied (row rename value) (List.mem_map.mpr ⟨value,member,rfl⟩)
    simpa only [row,eval_linear] using result
  · intro satisfied value member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    simpa only [row,eval_linear] using satisfied original present

theorem step_run (rename : Nat → Nat) (injective : Function.Injective rename)
    (base : Nat → F) (value : Step) (column : Nat) :
    (step rename value).run base (rename column)=value.run (fun index => base (rename index)) column := by
  have equality (left right : Nat) : rename left=rename right ↔ left=right := injective.eq_iff
  cases value with
  | square input remainder output =>
    simp [step,Step.run,extendSquare,patchAssignment,equality,eval_linear]
  | product left right remainder output auxiliary =>
    simp [step,Step.run,ScalarCompletion.extendProduct,ScalarCompletion.productValues,patchAssignment,equality,eval_linear]
  | equal left right => rfl
  | squareEqual input target => rfl

theorem run_steps (rename : Nat → Nat) (injective : Function.Injective rename)
    (base : Nat → F) (values : List Step) :
    (fun column => run base (steps rename values) (rename column))=
      run (fun column => base (rename column)) values := by
  induction values generalizing base with
  | nil => rfl
  | cons head tail ih =>
    change (fun column => run ((step rename head).run base) (steps rename tail) (rename column))=
      run (head.run (fun column => base (rename column))) tail
    rw [ih]
    congr 1
    funext column
    exact step_run rename injective base head column

theorem completed_rows (rename : Nat → Nat) (injective : Function.Injective rename)
    (base : Nat → F) (program : List Step) (original : List Row)
    (completed : Satisfies (run (fun column => base (rename column)) program) original) :
    Satisfies (run base (steps rename program)) (rows rename original) := by
  apply (satisfies_rows rename _ original).mpr
  rw [run_steps rename injective base program]
  exact completed

theorem fixed_preserved (rename : Nat → Nat) (injective : Function.Injective rename)
    (base : Nat → F) (program : List Step) (column : Nat) (fixed : rename column=column)
    (preserved : run (fun index => base (rename index)) program column=base (rename column)) :
    run base (steps rename program) column=base column := by
  have equality := congrFun (run_steps rename injective base program) column
  simpa only [fixed] using equality.trans preserved

end ShielddSecurity.CompilerColumnRenaming05
set_option pp.all true in
#check @ShielddSecurity.CompilerColumnRenaming05.eval_linear
#print axioms ShielddSecurity.CompilerColumnRenaming05.eval_linear
set_option pp.all true in
#check @ShielddSecurity.CompilerColumnRenaming05.satisfies_rows
#print axioms ShielddSecurity.CompilerColumnRenaming05.satisfies_rows
set_option pp.all true in
#check @ShielddSecurity.CompilerColumnRenaming05.step_run
#print axioms ShielddSecurity.CompilerColumnRenaming05.step_run
set_option pp.all true in
#check @ShielddSecurity.CompilerColumnRenaming05.run_steps
#print axioms ShielddSecurity.CompilerColumnRenaming05.run_steps
set_option pp.all true in
#check @ShielddSecurity.CompilerColumnRenaming05.completed_rows
#print axioms ShielddSecurity.CompilerColumnRenaming05.completed_rows
set_option pp.all true in
#check @ShielddSecurity.CompilerColumnRenaming05.fixed_preserved
#print axioms ShielddSecurity.CompilerColumnRenaming05.fixed_preserved
