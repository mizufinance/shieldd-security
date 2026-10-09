import ShielddSecurity.Compiler

set_option maxHeartbeats 200000

namespace ShielddSecurity.RowLinearSubstitution

/-- Substitute each source column by its actual complete linear expression.
This is needed when an owned selector fuses several physical columns. -/
def linear (columns : Nat → Linear) (terms : Linear) : Linear :=
  terms.flatMap (fun term => scaleLinear term.2 (columns term.1))

def row (columns : Nat → Linear) (source : Row) : Row :=
  ⟨linear columns source.a, linear columns source.b⟩

theorem eval_linear {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Linear) (terms : Linear) :
    eval rho (linear columns terms) = eval (fun column => eval rho (columns column)) terms := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      simp only [linear, List.flatMap_cons, eval_append, eval_scale, eval]
      exact congrArg (fun value => (term.2 : F) * eval rho (columns term.1) + value) ih

theorem satisfied_row {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Linear) (source : Row)
    (satisfied : Square (eval rho (row columns source).a) (eval rho (row columns source).b)) :
    Square (eval (fun column => eval rho (columns column)) source.a)
      (eval (fun column => eval rho (columns column)) source.b) := by
  simpa only [row, eval_linear] using satisfied

theorem checked_linear {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (columns : Nat → Linear) (source actual : Linear)
    (checked : Compiler.canonical p (linear columns source) = Compiler.canonical p actual) :
    eval (fun column => eval rho (columns column)) source = eval rho actual := by
  rw [← eval_linear]
  exact Compiler.canonical_equal rho (linear columns source) actual checked

theorem checked_rows {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (columns : Nat → Linear) (source actual : List Row)
    (checked : source.all (fun item => Compiler.checkRow p actual (row columns item)) = true)
    (satisfied : Satisfies rho actual) :
    Satisfies (fun column => eval rho (columns column)) source := by
  intro item member
  apply satisfied_row rho columns item
  exact Compiler.checked_row_sound rho actual (row columns item) satisfied
    ((List.all_eq_true.mp checked) item member)

theorem constant_preserved {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Linear) (binding : columns 0 = [(0, 1)]) (one : rho 0 = 1) :
    eval rho (columns 0) = 1 := by
  rw [binding]
  simp only [eval, one, Int.cast_one, one_mul, add_zero]

set_option pp.all true in
#check @eval_linear
#print axioms eval_linear
set_option pp.all true in
#check @satisfied_row
#print axioms satisfied_row
set_option pp.all true in
#check @checked_linear
#print axioms checked_linear
set_option pp.all true in
#check @checked_rows
#print axioms checked_rows
set_option pp.all true in
#check @constant_preserved
#print axioms constant_preserved

end ShielddSecurity.RowLinearSubstitution
