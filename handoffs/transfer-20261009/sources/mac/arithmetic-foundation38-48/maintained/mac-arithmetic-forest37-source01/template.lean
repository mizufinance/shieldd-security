import ShielddSecurity.CompilerFreshArithmetic35
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerArithmeticForest37
open Compiler
inductive Program where
  | leaf (recipes : List CompilerFreshArithmetic35.Recipe)
  | append (left right : Program)
def span : Program → Nat
  | .leaf recipes => CompilerFreshArithmetic35.span recipes
  | .append left right => span left+span right
def rows (floor : Nat) : Program → List Row
  | .leaf recipes => CompilerFreshArithmetic35.rows floor recipes
  | .append left right => rows floor left++rows (floor+span left) right
def rowAt (floor : Nat) : Program → Nat → Option Row
  | .leaf recipes,index => (CompilerFreshArithmetic35.rows floor recipes)[index]?
  | .append left right,index =>
    if index<span left then rowAt floor left index else rowAt (floor+span left) right (index-span left)
def check (copy floor : Nat) : Program → Bool
  | .leaf recipes => CompilerFreshArithmetic35.check copy floor recipes
  | .append left right => check copy floor left && check copy (floor+span left) right
variable {F : Type} [Field F]
def run (floor : Nat) (base : Nat → F) : Program → Nat → F
  | .leaf recipes => CompilerFreshArithmetic35.run floor base recipes
  | .append left right => run (floor+span left) (run floor base left) right
theorem outside (program : Program) (floor : Nat) (base : Nat → F) (column : Nat)
    (bound : column<floor ∨ floor+span program≤column) : run floor base program column=base column := by
  induction program generalizing floor base with
  | leaf recipes => exact CompilerFreshArithmetic35.run_outside recipes floor base column bound
  | append left right ihLeft ihRight =>
    change run (floor+span left) (run floor base left) right column=base column
    change column<floor ∨ floor+(span left+span right)≤column at bound
    rw [ihRight (floor+span left) (run floor base left) (by omega),ihLeft floor base (by omega)]
theorem support (program : Program) (copy floor : Nat) (checked : check copy floor program=true)
    (row : Row) (member : row∈rows floor program) (term : Nat×Int) (present : term∈row.a++row.b) :
    term.1<floor+span program ∨ term.1=copy := by
  induction program generalizing floor with
  | leaf recipes => exact CompilerFreshArithmetic35.row_support recipes copy floor checked row member term present
  | append left right ihLeft ihRight =>
    have parts := Bool.and_eq_true_iff.mp checked
    rcases List.mem_append.mp member with member|member
    · have found:=ihLeft floor parts.1 member
      change term.1<floor+(span left+span right) ∨ term.1=copy
      omega
    · have found:=ihRight (floor+span left) parts.2 member
      change term.1<floor+(span left+span right) ∨ term.1=copy
      omega
theorem complete (program : Program) (copy floor : Nat) (base : Nat → F)
    (checked : check copy floor program=true) (below : floor+span program≤copy) (four : (4:F)≠0) :
    Satisfies (run floor base program) (rows floor program) := by
  induction program generalizing floor base with
  | leaf recipes => exact CompilerFreshArithmetic35.complete recipes copy floor base checked below four
  | append left right ihLeft ihRight =>
    have parts := Bool.and_eq_true_iff.mp checked
    change floor+(span left+span right)≤copy at below
    have first:=ihLeft floor base parts.1 (by omega)
    have later:=ihRight (floor+span left) (run floor base left) parts.2 (by omega)
    intro row member
    rcases List.mem_append.mp member with member|member
    · have agrees (terms : Linear) (included : ∀ term∈terms,term∈row.a++row.b) :
        eval (run (floor+span left) (run floor base left) right) terms=eval (run floor base left) terms := by
        apply eval_agrees
        intro term present
        have old:=support left copy floor parts.1 row member term (included term present)
        apply outside right (floor+span left) (run floor base left) term.1
        omega
      change Square (eval (run (floor+span left) (run floor base left) right) row.a)
        (eval (run (floor+span left) (run floor base left) right) row.b)
      rw [agrees row.a (by intro term present;exact List.mem_append_left _ present),
        agrees row.b (by intro term present;exact List.mem_append_right _ present)]
      exact first row member
    · exact later row member
omit [Field F] in
theorem rowAt_mem (program : Program) (floor index : Nat) (row : Row) (found : rowAt floor program index=some row) :
    row∈rows floor program := by
  induction program generalizing floor index with
  | leaf recipes => exact List.mem_of_getElem? found
  | append left right ihLeft ihRight =>
    change (if index<span left then rowAt floor left index else rowAt (floor+span left) right (index-span left))=some row at found
    split_ifs at found with before
    · exact List.mem_append_left _ (ihLeft floor index found)
    · exact List.mem_append_right _ (ihRight (floor+span left) (index-span left) found)
omit [Field F] in
theorem recipe_rows_length (recipe : CompilerFreshArithmetic35.Recipe) (floor : Nat) : (recipe.rows floor).length=recipe.width := by
  cases recipe <;> rfl
omit [Field F] in
theorem leaf_rows_length (recipes : List CompilerFreshArithmetic35.Recipe) (floor : Nat) :
    (CompilerFreshArithmetic35.rows floor recipes).length=CompilerFreshArithmetic35.span recipes := by
  induction recipes generalizing floor with
  | nil => rfl
  | cons recipe tail ih =>
    simp only [CompilerFreshArithmetic35.rows,List.length_append,recipe_rows_length,ih,CompilerFreshArithmetic35.span]
omit [Field F] in
theorem rows_length (program : Program) (floor : Nat) : (rows floor program).length=span program := by
  induction program generalizing floor with
  | leaf recipes => exact leaf_rows_length recipes floor
  | append left right ihLeft ihRight =>
    simp only [rows,List.length_append,ihLeft,ihRight,span]
omit [Field F] in
theorem every_position (program : Program) (floor index : Nat) (bound : index<span program) :
    ∃ row : Row,rowAt floor program index=some row := by
  induction program generalizing floor index with
  | leaf recipes =>
    have before : index<(CompilerFreshArithmetic35.rows floor recipes).length := by rw [leaf_rows_length];exact bound
    exact ⟨(CompilerFreshArithmetic35.rows floor recipes)[index],List.getElem?_eq_getElem before⟩
  | append left right ihLeft ihRight =>
    change index<span left+span right at bound
    by_cases before : index<span left
    · obtain ⟨row,found⟩:=ihLeft floor index before
      exact ⟨row,by simpa only [rowAt,if_pos before] using found⟩
    · have later : index-span left<span right := by omega
      obtain ⟨row,found⟩:=ihRight (floor+span left) (index-span left) later
      exact ⟨row,by simpa only [rowAt,if_neg before] using found⟩
def SatisfiesAt (rho : Nat → F) (floor : Nat) (program : Program) : Prop :=
  ∀ index<span program,∀ row : Row,rowAt floor program index=some row → Square (eval rho row.a) (eval rho row.b)
theorem complete_indexed (program : Program) (copy floor : Nat) (base : Nat → F)
    (checked : check copy floor program=true) (below : floor+span program≤copy) (four : (4:F)≠0) :
    SatisfiesAt (run floor base program) floor program := by
  intro index bound row found
  exact complete program copy floor base checked below four row (rowAt_mem program floor index row found)
end ShielddSecurity.CompilerArithmeticForest37
