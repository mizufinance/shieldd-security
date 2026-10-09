import ShielddSecurity.Compiler

set_option maxHeartbeats 200000

namespace ShielddSecurity.RowRenaming

def linear (columns : Nat → Nat) (terms : Linear) : Linear :=
  terms.map (fun term => (columns term.1, term.2))

def row (columns : Nat → Nat) (source : Row) : Row :=
  ⟨linear columns source.a, linear columns source.b⟩

theorem eval_linear {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Nat) (terms : Linear) :
    eval rho (linear columns terms) = eval (fun column => rho (columns column)) terms := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      simp only [linear, List.map_cons, eval]
      exact congrArg (fun value => (term.2 : F) * rho (columns term.1) + value) ih

theorem satisfied_row {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Nat) (source : Row)
    (satisfied : Square (eval rho (row columns source).a)
      (eval rho (row columns source).b)) :
    Square (eval (fun column => rho (columns column)) source.a)
      (eval (fun column => rho (columns column)) source.b) := by
  simpa only [row, eval_linear] using satisfied

theorem satisfied_rows {F : Type} [Field F] (rho : Nat → F)
    (columns : Nat → Nat) (source : List Row) (actual : List Row)
    (included : ∀ item ∈ source, row columns item ∈ actual)
    (satisfied : Satisfies rho actual) :
    Satisfies (fun column => rho (columns column)) source := by
  intro item member
  exact satisfied_row rho columns item (satisfied (row columns item) (included item member))

theorem checked_linear {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (columns : Nat → Nat) (source actual : Linear)
    (checked : Compiler.canonical p (linear columns source) = Compiler.canonical p actual) :
    eval (fun column => rho (columns column)) source = eval rho actual := by
  rw [← eval_linear]
  exact Compiler.canonical_equal rho (linear columns source) actual checked

theorem checked_rows {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (columns : Nat → Nat) (source actual : List Row)
    (checked : source.all (fun item => Compiler.checkRow p actual (row columns item)) = true)
    (satisfied : Satisfies rho actual) :
    Satisfies (fun column => rho (columns column)) source := by
  intro item member
  apply satisfied_row rho columns item
  exact Compiler.checked_row_sound rho actual (row columns item) satisfied
    ((List.all_eq_true.mp checked) item member)

set_option pp.all true in
#check @eval_linear
#print axioms eval_linear
set_option pp.all true in
#check @satisfied_row
#print axioms satisfied_row
set_option pp.all true in
#check @satisfied_rows
#print axioms satisfied_rows
set_option pp.all true in
#check @checked_linear
#print axioms checked_linear
set_option pp.all true in
#check @checked_rows
#print axioms checked_rows

end ShielddSecurity.RowRenaming
