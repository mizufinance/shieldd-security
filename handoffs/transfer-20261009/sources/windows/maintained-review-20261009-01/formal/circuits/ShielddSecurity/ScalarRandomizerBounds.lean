import ShielddSecurity.ScalarRandomizerCompletion

set_option maxHeartbeats 500000

namespace ShielddSecurity.ScalarRandomizerBounds

def LinearBelow (bound : Nat) (terms : Linear) : Prop :=
  ∀ term ∈ terms, term.1 < bound

def RowsBelow (bound : Nat) (rows : List Row) : Prop :=
  ∀ row ∈ rows, LinearBelow bound (row.a ++ row.b)

theorem emitted_append (front back : List CompilerCompletion.Step) :
    CompilerCompletion.emitted (front ++ back) =
      CompilerCompletion.emitted front ++ CompilerCompletion.emitted back := by
  induction front with
  | nil => rfl
  | cons stage tail ih =>
      simp only [List.cons_append, CompilerCompletion.emitted, ih, List.append_assoc]

theorem rows_append (bound : Nat) (left right : List Row)
    (first : RowsBelow bound left) (second : RowsBelow bound right) :
    RowsBelow bound (left ++ right) := by
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact first row member
  · exact second row member

theorem rows_mono (first second : Nat) (rows : List Row)
    (below : RowsBelow first rows) (bound : first ≤ second) : RowsBelow second rows := by
  intro row member term present
  exact Nat.lt_of_lt_of_le (below row member term present) bound

private theorem weighted_below (bound : Nat) (columns : List Nat) (weight : Int)
    (below : ∀ column ∈ columns, column < bound) : LinearBelow bound (weighted columns weight) := by
  induction columns generalizing weight with
  | nil => intro term member; cases member
  | cons column tail ih =>
      intro term member
      simp only [weighted, List.mem_cons] at member
      rcases member with rfl | member
      · exact below column (by simp)
      · exact ih (weight * 2)
          (by intro next member; exact below next (List.mem_cons_of_mem _ member)) term member

theorem initial_rows_below (value start upper : Nat) (valueBelow : value < upper)
    (bitsBelow : (List.range' start 252).all (fun column => decide (column < upper)) = true) :
    RowsBelow upper (ScalarRandomizerCompletion.initialRows value start) := by
  have columns : ∀ column ∈ List.range' start 252, column < upper := by
    intro column member
    exact of_decide_eq_true (List.all_eq_true.mp bitsBelow column member)
  intro row member term present
  simp only [ScalarRandomizerCompletion.initialRows, List.mem_append,
    List.mem_singleton] at member
  rcases member with boolean | rfl
  · obtain ⟨column, inside, rfl⟩ := List.mem_map.mp boolean
    simp only [booleanRow, List.mem_append, List.mem_singleton] at present
    rcases present with rfl | rfl <;> exact columns column inside
  · simp only [reconstructionRow, List.append_nil, List.mem_cons] at present
    rcases present with rfl | present
    · exact valueBelow
    · exact weighted_below upper _ 1 columns term present

private theorem linear_append (bound : Nat) (left right : Linear)
    (hl : LinearBelow bound left) (hr : LinearBelow bound right) :
    LinearBelow bound (left ++ right) := by
  intro term member
  rcases List.mem_append.mp member with member | member
  · exact hl term member
  · exact hr term member

private theorem linear_scale (bound : Nat) (factor : Int) (terms : Linear)
    (below : LinearBelow bound terms) : LinearBelow bound (scaleLinear factor terms) := by
  intro term member
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  exact below original inside

private theorem linear_mono (first second : Nat) (terms : Linear)
    (below : LinearBelow first terms) (bound : first ≤ second) : LinearBelow second terms := by
  intro term member
  exact Nat.lt_of_lt_of_le (below term member) bound

private theorem product_rows_below (left right remainder : Linear) (output auxiliary : Nat)
    (inputs : LinearBelow output (left ++ right ++ remainder)) (outputs : output < auxiliary) :
    RowsBelow (auxiliary + 1) (ScalarCompletion.productRows left right remainder output auxiliary) := by
  have inputBound : LinearBelow (auxiliary + 1) (left ++ right ++ remainder) :=
    linear_mono _ _ _ inputs (by omega)
  have leftBound : LinearBelow (auxiliary + 1) left := by
    intro term member
    exact inputBound term (List.mem_append_left remainder (List.mem_append_left right member))
  have rightBound : LinearBelow (auxiliary + 1) right := by
    intro term member
    exact inputBound term (List.mem_append_left remainder (List.mem_append_right left member))
  have remainderBound : LinearBelow (auxiliary + 1) remainder := by
    intro term member
    exact inputBound term (List.mem_append_right (left ++ right) member)
  have outputBound : LinearBelow (auxiliary + 1) [(output, 1)] := by
    intro term member
    simp only [List.mem_singleton] at member
    subst term
    exact Nat.lt_trans outputs (Nat.lt_succ_self auxiliary)
  have auxiliaryBound : LinearBelow (auxiliary + 1) [(auxiliary, 1)] := by
    intro term member
    simp only [List.mem_singleton] at member
    subst term
    exact Nat.lt_succ_self auxiliary
  intro row member
  simp only [ScalarCompletion.productRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact linear_append _ _ _
      (linear_append _ _ _ leftBound (linear_scale _ (-1) right rightBound)) auxiliaryBound
  · exact linear_append _ _ _ (linear_append _ _ _ leftBound rightBound)
      (linear_append _ _ _ auxiliaryBound
        (linear_scale _ 4 _ (linear_append _ _ _ outputBound remainderBound)))

/-- Each concrete call checks at most16 captured products. The lower support
bound for previous chunks is carried symbolically, rather than rechecking
hundreds of earlier row/column pairs at every new stage. -/
def checkBounded : Nat → Nat → List CompilerCompletion.Step → Bool
  | lower, upper, [] => decide (lower ≤ upper)
  | lower, upper, .product left right remainder output auxiliary :: tail =>
      decide (lower ≤ output ∧ output < auxiliary) &&
      (left ++ right ++ remainder).all (fun term => decide (term.1 < output)) &&
      checkBounded (auxiliary + 1) upper tail
  | _, _, _ :: _ => false

def checkProtected (kept : List Nat) (stages : List CompilerCompletion.Step) : Bool :=
  stages.all (fun stage => kept.all (fun column => decide (column ∉ stage.writes)))

theorem protected_certificate (kept : List Nat) (stages : List CompilerCompletion.Step)
    (checked : checkProtected kept stages = true) :
    ∀ stage ∈ stages, ∀ column ∈ kept, column ∉ stage.writes := by
  intro stage member column inside
  exact of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column inside)

private theorem checked_bounds (lower upper : Nat) (stages : List CompilerCompletion.Step)
    (checked : checkBounded lower upper stages = true) : lower ≤ upper := by
  induction stages generalizing lower with
  | nil => exact of_decide_eq_true checked
  | cons stage tail ih =>
      cases stage with
      | square input remainder output => simp [checkBounded] at checked
      | equal left right => simp [checkBounded] at checked
      | squareEqual input target => simp [checkBounded] at checked
      | product left right remainder output auxiliary =>
          simp only [checkBounded,Bool.and_eq_true,decide_eq_true_eq] at checked
          have remaining := ih (auxiliary + 1) checked.2
          omega

theorem bounded_rows (lower upper : Nat) (stages : List CompilerCompletion.Step)
    (checked : checkBounded lower upper stages = true) :
    RowsBelow upper (CompilerCompletion.emitted stages) := by
  induction stages generalizing lower with
  | nil => intro row member; cases member
  | cons stage tail ih =>
      cases stage with
      | square input remainder output => simp [checkBounded] at checked
      | equal left right => simp [checkBounded] at checked
      | squareEqual input target => simp [checkBounded] at checked
      | product left right remainder output auxiliary =>
          simp only [checkBounded,Bool.and_eq_true,decide_eq_true_eq] at checked
          have inputBounds : LinearBelow output (left ++ right ++ remainder) := by
            intro term member
            exact of_decide_eq_true (List.all_eq_true.mp checked.1.2 term member)
          have current := product_rows_below left right remainder output auxiliary inputBounds checked.1.1.2
          have remaining := ih (auxiliary + 1) checked.2
          have upperBound := checked_bounds (auxiliary + 1) upper tail checked.2
          intro row member
          rcases List.mem_append.mp member with now | later
          · exact linear_mono _ _ _ (current row now) upperBound
          · exact remaining row later

theorem bounded_ordered (lower upper : Nat) (stages : List CompilerCompletion.Step)
    (kept : List Nat) (prior : List Row)
    (checked : checkBounded lower upper stages = true)
    (below : RowsBelow lower prior)
    (protection : ∀ stage ∈ stages, ∀ column ∈ kept, column ∉ stage.writes) :
    CompilerCompletion.Topological kept prior stages := by
  induction stages generalizing lower prior with
  | nil => trivial
  | cons stage tail ih =>
      cases stage with
      | square input remainder output => simp [checkBounded] at checked
      | equal left right => simp [checkBounded] at checked
      | squareEqual input target => simp [checkBounded] at checked
      | product left right remainder output auxiliary =>
          simp only [checkBounded,Bool.and_eq_true,decide_eq_true_eq] at checked
          have inputBounds : LinearBelow output (left ++ right ++ remainder) := by
            intro term member
            exact of_decide_eq_true (List.all_eq_true.mp checked.1.2 term member)
          have shape : (CompilerCompletion.Step.product left right remainder output auxiliary).Shape := by
            refine ⟨by omega, ?_⟩
            intro term member
            have bound := inputBounds term member
            simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or]
            constructor <;> omega
          have previous : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
              term.1 ∉ [output, auxiliary] := by
            intro row member term present
            have bound := below row member term present
            simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or]
            constructor <;> omega
          have current := product_rows_below left right remainder output auxiliary inputBounds checked.1.1.2
          have extended : RowsBelow (auxiliary + 1)
              (prior ++ ScalarCompletion.productRows left right remainder output auxiliary) := by
            intro row member
            rcases List.mem_append.mp member with old | now
            · exact linear_mono _ _ _ (below row old) (by omega)
            · exact current row now
          refine ⟨shape, protection _ (by simp), previous, ?_⟩
          exact ih (auxiliary + 1) _ checked.2 extended
            (by intro step member; exact protection step (List.mem_cons_of_mem _ member))

set_option pp.all true in
#check @emitted_append
#print axioms emitted_append
set_option pp.all true in
#check @rows_append
#print axioms rows_append
set_option pp.all true in
#check @rows_mono
#print axioms rows_mono
set_option pp.all true in
#check @initial_rows_below
#print axioms initial_rows_below
set_option pp.all true in
#check @protected_certificate
#print axioms protected_certificate
set_option pp.all true in
#check @bounded_rows
#print axioms bounded_rows
set_option pp.all true in
#check @bounded_ordered
#print axioms bounded_ordered

end ShielddSecurity.ScalarRandomizerBounds
