import ShielddSecurity.ScalarComparisonBounds

set_option maxHeartbeats 300000

namespace ShielddSecurity.ScalarChainComposition

theorem row_monotone (p : Nat) (source actual : List Row)
    (included : ∀ item ∈ source, item ∈ actual) (expected : Row)
    (checked : Compiler.checkRow p source expected = true) :
    Compiler.checkRow p actual expected = true := by
  obtain ⟨item, member, accepted⟩ := List.any_eq_true.mp checked
  exact List.any_eq_true.mpr ⟨item, included item member, accepted⟩

theorem product_monotone (p : Nat) (source actual : List Row)
    (included : ∀ item ∈ source, item ∈ actual)
    (left right output : Linear) (data : ScalarRows.ProductData)
    (checked : ScalarRows.checkProduct p source left right output data = true) :
    ScalarRows.checkProduct p actual left right output data = true := by
  cases data with
  | foldedLeft coefficient => exact checked
  | foldedRight coefficient => exact checked
  | square =>
      simp only [ScalarRows.checkProduct, Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1, row_monotone p source actual included _ checked.2⟩
  | product auxiliary =>
      simp only [ScalarRows.checkProduct, Bool.and_eq_true] at checked ⊢
      exact ⟨row_monotone p source actual included _ checked.1,
        row_monotone p source actual included _ checked.2⟩

theorem step_monotone (p : Nat) (source actual : List Row)
    (included : ∀ item ∈ source, item ∈ actual) (step : ScalarRows.StepData)
    (checked : ScalarRows.checkStep p source step = true) :
    ScalarRows.checkStep p actual step = true := by
  simp only [ScalarRows.checkStep, Bool.and_eq_true] at checked ⊢
  exact ⟨checked.1, product_monotone p source actual included _ _ _ _ checked.2⟩

theorem chain_monotone (p : Nat) (source actual : List Row)
    (included : ∀ item ∈ source, item ∈ actual)
    (initial : Linear) (steps : List ScalarRows.StepData)
    (checked : ScalarRows.checkChain p source initial steps = true) :
    ScalarRows.checkChain p actual initial steps = true := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step tail ih =>
      simp only [ScalarRows.checkChain, Bool.and_eq_true] at checked ⊢
      exact ⟨⟨checked.1.1, step_monotone p source actual included step checked.1.2⟩,
        ih step.after checked.2⟩

theorem chain_append (p : Nat) (rows : List Row) (initial : Linear)
    (left right : List ScalarRows.StepData)
    (first : ScalarRows.checkChain p rows initial left = true)
    (second : ScalarRows.checkChain p rows
      (ScalarComparisonBounds.endpoint initial left) right = true) :
    ScalarRows.checkChain p rows initial (left ++ right) = true := by
  induction left generalizing initial with
  | nil => exact second
  | cons step tail ih =>
      simp only [ScalarRows.checkChain, Bool.and_eq_true] at first
      simp only [List.cons_append, ScalarRows.checkChain, Bool.and_eq_true]
      exact ⟨first.1, ih step.after first.2 second⟩

theorem bits_monotone (p : Nat) (source actual : List Row)
    (included : ∀ item ∈ source, item ∈ actual) (bits : List Linear)
    (checked : ScalarBits.checkBits p source bits = true) :
    ScalarBits.checkBits p actual bits = true := by
  apply List.all_eq_true.mpr
  intro bit member
  exact row_monotone p source actual included _ ((List.all_eq_true.mp checked) bit member)

theorem bits_append (p : Nat) (rows : List Row) (left right : List Linear)
    (first : ScalarBits.checkBits p rows left = true)
    (second : ScalarBits.checkBits p rows right = true) :
    ScalarBits.checkBits p rows (left ++ right) = true := by
  apply List.all_eq_true.mpr
  intro bit member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact (List.all_eq_true.mp first) bit leftMember
  · exact (List.all_eq_true.mp second) bit rightMember

theorem endpoint_append (initial : Linear) (left right : List ScalarRows.StepData) :
    ScalarComparisonBounds.endpoint initial (left ++ right) =
      ScalarComparisonBounds.endpoint (ScalarComparisonBounds.endpoint initial left) right := by
  induction left generalizing initial with
  | nil => rfl
  | cons step tail ih => exact ih step.after

set_option pp.all true in
#check @row_monotone
#print axioms row_monotone
set_option pp.all true in
#check @product_monotone
#print axioms product_monotone
set_option pp.all true in
#check @step_monotone
#print axioms step_monotone
set_option pp.all true in
#check @chain_monotone
#print axioms chain_monotone
set_option pp.all true in
#check @chain_append
#print axioms chain_append
set_option pp.all true in
#check @bits_monotone
#print axioms bits_monotone
set_option pp.all true in
#check @bits_append
#print axioms bits_append
set_option pp.all true in
#check @endpoint_append
#print axioms endpoint_append

end ShielddSecurity.ScalarChainComposition
