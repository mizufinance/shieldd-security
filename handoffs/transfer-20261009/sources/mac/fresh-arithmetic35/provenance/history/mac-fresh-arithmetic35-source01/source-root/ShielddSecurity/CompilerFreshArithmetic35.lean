import ShielddSecurity.CompilerSegmentCompletion11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerFreshArithmetic35
open Compiler CompilerCompletion
variable {F : Type} [Field F]
inductive Recipe where
  | square (input : Linear)
  | pair (minus plus : Linear)
def Recipe.width : Recipe → Nat
  | .square _ => 1
  | .pair _ _ => 2
def Recipe.inputs : Recipe → Linear
  | .square input => input
  | .pair minus plus => minus++plus
def Recipe.rows (floor : Nat) : Recipe → List Row
  | .square input => [⟨input,[(floor,1)]⟩]
  | .pair minus plus => [⟨minus,[(floor+1,1)]⟩,⟨plus,[(floor,4),(floor+1,1)]⟩]
def pairValues (base : Nat → F) (minus plus : Linear) (floor column : Nat) : F :=
  if column=floor then ((eval base plus)^2-(eval base minus)^2)/4
  else if column=floor+1 then (eval base minus)^2 else base column
def Recipe.run (floor : Nat) (base : Nat → F) : Recipe → Nat → F
  | .square input => extendSquare base input [] floor
  | .pair minus plus => patchAssignment base (pairValues base minus plus floor) [floor,floor+1]
def Recipe.Valid (copy floor : Nat) (recipe : Recipe) : Prop :=
  ∀ term∈recipe.inputs,term.1<floor ∨ term.1=copy
def Recipe.check (copy floor : Nat) (recipe : Recipe) : Bool :=
  recipe.inputs.all (fun term => decide (term.1<floor ∨ term.1=copy))
theorem check_sound (copy floor : Nat) (recipe : Recipe) (checked : recipe.check copy floor=true) : recipe.Valid copy floor := by
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)
theorem width_pos (recipe : Recipe) : 0<recipe.width := by cases recipe <;> decide
theorem recipe_outside (recipe : Recipe) (floor : Nat) (base : Nat → F) (column : Nat)
    (outside : column<floor ∨ floor+recipe.width≤column) : recipe.run floor base column=base column := by
  cases recipe with
  | square input =>
    exact patchAssignment_preserves base _ [floor] column (by simp only [List.mem_singleton];change column≠floor;change column<floor ∨ floor+1≤column at outside;omega)
  | pair minus plus =>
    exact patchAssignment_preserves base _ [floor,floor+1] column (by simp only [List.mem_cons,List.mem_singleton];change ¬(column=floor ∨ column=floor+1);change column<floor ∨ floor+2≤column at outside;omega)
theorem recipe_complete (recipe : Recipe) (copy floor : Nat) (base : Nat → F)
    (valid : recipe.Valid copy floor) (below : floor+recipe.width≤copy) (four : (4:F)≠0) :
    Satisfies (recipe.run floor base) (recipe.rows floor) := by
  cases recipe with
  | square input =>
    apply square_complete base input [] floor
    intro term member
    have before := valid term (by simpa only [Recipe.inputs,List.append_nil] using member)
    change floor+1≤copy at below
    omega
  | pair minus plus =>
    let rho := patchAssignment base (pairValues base minus plus floor) [floor,floor+1]
    have agrees (terms : Linear) (included : ∀ term∈terms,term∈minus++plus) : eval rho terms=eval base terms := by
      apply eval_agrees
      intro term member
      apply patchAssignment_preserves base _ [floor,floor+1] term.1
      have old := valid term (included term member)
      change floor+2≤copy at below
      simp only [List.mem_cons,List.mem_singleton]
      omega
    have minusValue := agrees minus (by intro term member;exact List.mem_append_left _ member)
    have plusValue := agrees plus (by intro term member;exact List.mem_append_right _ member)
    have output : rho floor=((eval base plus)^2-(eval base minus)^2)/4 := by simp [rho,patchAssignment,pairValues]
    have auxiliary : rho (floor+1)=(eval base minus)^2 := by simp [rho,patchAssignment,pairValues]
    change Satisfies rho [⟨minus,[(floor+1,1)]⟩,⟨plus,[(floor,4),(floor+1,1)]⟩]
    intro row member
    simp only [List.mem_cons,List.mem_singleton] at member
    rcases member with rfl|rfl
    · change Square (eval rho minus) (eval rho [(floor+1,1)])
      simp only [Square,eval,Int.cast_one,one_mul,add_zero,minusValue,auxiliary,pow_two]
    · change Square (eval rho plus) (eval rho [(floor,4),(floor+1,1)])
      simp only [Square,eval,Int.cast_ofNat,Int.cast_one,one_mul,add_zero,plusValue,output,auxiliary]
      have cancel := div_mul_cancel₀ ((eval base plus)^2-(eval base minus)^2) four
      rw [mul_comm (4:F),cancel]
      ring
def span : List Recipe → Nat
  | [] => 0
  | recipe::tail => recipe.width+span tail
def rows (floor : Nat) : List Recipe → List Row
  | [] => []
  | recipe::tail => recipe.rows floor++rows (floor+recipe.width) tail
def run (floor : Nat) (base : Nat → F) : List Recipe → Nat → F
  | [] => base
  | recipe::tail => run (floor+recipe.width) (recipe.run floor base) tail
def check (copy floor : Nat) : List Recipe → Bool
  | [] => true
  | recipe::tail => recipe.check copy floor && check copy (floor+recipe.width) tail
theorem run_outside (recipes : List Recipe) (floor : Nat) (base : Nat → F) (column : Nat)
    (outside : column<floor ∨ floor+span recipes≤column) : run floor base recipes column=base column := by
  induction recipes generalizing floor base with
  | nil => rfl
  | cons recipe tail ih =>
    change run (floor+recipe.width) (recipe.run floor base) tail column=base column
    rw [ih (floor+recipe.width) (recipe.run floor base) (by simp only [span] at outside;omega),recipe_outside recipe floor base column (by simp only [span] at outside;omega)]
theorem row_support (recipes : List Recipe) (copy floor : Nat) (checked : check copy floor recipes=true)
    (row : Row) (member : row∈rows floor recipes) (term : Nat×Int) (present : term∈row.a++row.b) :
    term.1<floor+span recipes ∨ term.1=copy := by
  induction recipes generalizing floor with
  | nil => simp only [rows,List.not_mem_nil] at member
  | cons recipe tail ih =>
    have parts := Bool.and_eq_true_iff.mp checked
    rcases List.mem_append.mp member with member|member
    · have valid := check_sound copy floor recipe parts.1
      cases recipe with
      | square input =>
        have equal : row=⟨input,[(floor,1)]⟩ := by simpa only [Recipe.rows,List.mem_singleton] using member
        subst row
        rcases List.mem_append.mp present with old|fresh
        · have h:=valid term old;change term.1<floor+(1+span tail) ∨ term.1=copy;omega
        · have h : term=(floor,1) := by simpa only [List.mem_singleton] using fresh
          subst term;exact Or.inl (by change floor<floor+(1+span tail);omega)
      | pair minus plus =>
        have m : row=⟨minus,[(floor+1,1)]⟩ ∨ row=⟨plus,[(floor,4),(floor+1,1)]⟩ := by simpa only [Recipe.rows,List.mem_cons,List.mem_singleton] using member
        rcases m with rfl|rfl
        all_goals
          rcases List.mem_append.mp present with old|fresh
          · have h:=valid term (by simp only [Recipe.inputs];first | exact List.mem_append_left _ old | exact List.mem_append_right _ old)
            change term.1<floor+(2+span tail) ∨ term.1=copy;omega
          · simp only [List.mem_cons,List.mem_singleton] at fresh
            rcases fresh with fresh|fresh
            all_goals subst term;exact Or.inl (by change _<floor+(2+span tail);omega)
    · have h:=ih (floor+recipe.width) parts.2 row member term present
      simp only [span];omega
theorem complete (recipes : List Recipe) (copy floor : Nat) (base : Nat → F)
    (checked : check copy floor recipes=true) (below : floor+span recipes≤copy) (four : (4:F)≠0) :
    Satisfies (run floor base recipes) (rows floor recipes) := by
  induction recipes generalizing floor base with
  | nil => intro row member;simp only [rows,List.not_mem_nil] at member
  | cons recipe tail ih =>
    have parts := Bool.and_eq_true_iff.mp checked
    have bound : floor+recipe.width≤copy := by simp only [span] at below;omega
    have first := recipe_complete recipe copy floor base (check_sound copy floor recipe parts.1) bound four
    have later := ih (floor+recipe.width) (recipe.run floor base) parts.2 (by simp only [span] at below;omega)
    intro row member
    rcases List.mem_append.mp member with member|member
    · have values : eval (run (floor+recipe.width) (recipe.run floor base) tail) row.a=eval (recipe.run floor base) row.a ∧
          eval (run (floor+recipe.width) (recipe.run floor base) tail) row.b=eval (recipe.run floor base) row.b := by
        constructor
        all_goals
          apply eval_agrees
          intro term present
          have support := row_support [recipe] copy floor (by simpa only [check,Bool.and_true] using parts.1) row (by simpa only [rows,List.append_nil] using member) term (by first | exact List.mem_append_left _ present | exact List.mem_append_right _ present)
          apply run_outside tail (floor+recipe.width) _ term.1
          simp only [span,Nat.add_zero] at support
          omega
      change Square (eval (run (floor+recipe.width) (recipe.run floor base) tail) row.a) (eval (run (floor+recipe.width) (recipe.run floor base) tail) row.b)
      rw [values.1,values.2]
      exact first row member
    · exact later row member
end ShielddSecurity.CompilerFreshArithmetic35

set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe.width
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe.width
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe.inputs
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe.inputs
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe.rows
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe.rows
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.pairValues
#print axioms ShielddSecurity.CompilerFreshArithmetic35.pairValues
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe.run
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe.run
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe.Valid
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe.Valid
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.Recipe.check
#print axioms ShielddSecurity.CompilerFreshArithmetic35.Recipe.check
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.check_sound
#print axioms ShielddSecurity.CompilerFreshArithmetic35.check_sound
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.width_pos
#print axioms ShielddSecurity.CompilerFreshArithmetic35.width_pos
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.recipe_outside
#print axioms ShielddSecurity.CompilerFreshArithmetic35.recipe_outside
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.recipe_complete
#print axioms ShielddSecurity.CompilerFreshArithmetic35.recipe_complete
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.span
#print axioms ShielddSecurity.CompilerFreshArithmetic35.span
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.rows
#print axioms ShielddSecurity.CompilerFreshArithmetic35.rows
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.run
#print axioms ShielddSecurity.CompilerFreshArithmetic35.run
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.check
#print axioms ShielddSecurity.CompilerFreshArithmetic35.check
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.run_outside
#print axioms ShielddSecurity.CompilerFreshArithmetic35.run_outside
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.row_support
#print axioms ShielddSecurity.CompilerFreshArithmetic35.row_support
set_option pp.all true in
#check @ShielddSecurity.CompilerFreshArithmetic35.complete
#print axioms ShielddSecurity.CompilerFreshArithmetic35.complete
