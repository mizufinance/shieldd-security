import ShielddSecurity.ScalarChunkComposition

set_option maxHeartbeats 200000

namespace ShielddSecurity.ScalarRowTransport

/-- Transport finite checkers through exact canonical row certificates. Local
captured rows and emitted constructors may collect/order coefficients
differently. No row truth, hash or source-node identity is a premise. -/
theorem row (p : Nat) (localRows commonRows : List Row)
    (transport : ∀ actual ∈ localRows, Compiler.checkRow p commonRows actual = true)
    (expected : Row) (checked : Compiler.checkRow p localRows expected = true) :
    Compiler.checkRow p commonRows expected = true := by
  obtain ⟨actual,member,accepted⟩ := List.any_eq_true.mp checked
  have first := of_decide_eq_true accepted
  obtain ⟨target,present,canonical⟩ := List.any_eq_true.mp (transport actual member)
  have second := of_decide_eq_true canonical
  apply List.any_eq_true.mpr
  refine ⟨target,present,?_⟩
  simpa only [decide_eq_true_eq] using (And.intro (second.1.trans first.1) (second.2.trans first.2))

theorem product (p : Nat) (localRows commonRows : List Row)
    (transport : ∀ actual ∈ localRows, Compiler.checkRow p commonRows actual = true)
    (left right output : Linear) (data : ScalarRows.ProductData)
    (checked : ScalarRows.checkProduct p localRows left right output data = true) :
    ScalarRows.checkProduct p commonRows left right output data = true := by
  cases data with
  | foldedLeft coefficient => exact checked
  | foldedRight coefficient => exact checked
  | square =>
      simp only [ScalarRows.checkProduct,Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1,row p localRows commonRows transport _ checked.2⟩
  | product auxiliary =>
      simp only [ScalarRows.checkProduct,Bool.and_eq_true] at checked ⊢
      exact ⟨row p localRows commonRows transport _ checked.1,
        row p localRows commonRows transport _ checked.2⟩

theorem chain (p : Nat) (localRows commonRows : List Row)
    (transport : ∀ actual ∈ localRows, Compiler.checkRow p commonRows actual = true)
    (initial : Linear) (steps : List ScalarRows.StepData)
    (checked : ScalarRows.checkChain p localRows initial steps = true) :
    ScalarRows.checkChain p commonRows initial steps = true := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step tail ih =>
      simp only [ScalarRows.checkChain,Bool.and_eq_true] at checked ⊢
      have current : ScalarRows.checkStep p commonRows step = true := by
        simp only [ScalarRows.checkStep,Bool.and_eq_true] at checked ⊢
        exact ⟨checked.1.2.1,product p localRows commonRows transport _ _ _ _ checked.1.2.2⟩
      exact ⟨⟨checked.1.1,current⟩,ih step.after checked.2⟩

theorem bits (p : Nat) (localRows commonRows : List Row)
    (transport : ∀ actual ∈ localRows, Compiler.checkRow p commonRows actual = true)
    (bits : List Linear) (checked : ScalarBits.checkBits p localRows bits = true) :
    ScalarBits.checkBits p commonRows bits = true := by
  apply List.all_eq_true.mpr
  intro bit member
  exact row p localRows commonRows transport ⟨bit,bit⟩ (List.all_eq_true.mp checked bit member)

set_option pp.all true in
#check @row
#print axioms row
set_option pp.all true in
#check @product
#print axioms product
set_option pp.all true in
#check @chain
#print axioms chain
set_option pp.all true in
#check @bits
#print axioms bits

end ShielddSecurity.ScalarRowTransport
