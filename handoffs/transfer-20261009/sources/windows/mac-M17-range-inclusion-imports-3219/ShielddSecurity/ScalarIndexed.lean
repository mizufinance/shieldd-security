import ShielddSecurity.ScalarRows

set_option maxHeartbeats 500000

namespace ShielddSecurity.ScalarIndexed

variable {F : Type} [Field F]

/-- Check exactly the original selected row at a supplied index. A missing or
changed row fails; no scan canonicalizes unrelated relation rows. -/
def checkRowAt (p : Nat) (rows : List Row) (index : Nat) (expected : Row) : Bool :=
  match rows[index]? with
  | none => false
  | some actual => decide
      (Compiler.canonical p actual.a = Compiler.canonical p expected.a ∧
       Compiler.canonical p actual.b = Compiler.canonical p expected.b)

theorem checked_row_membership (p : Nat) (rows : List Row) (index : Nat) (expected : Row)
    (checked : checkRowAt p rows index expected = true) :
    Compiler.checkRow p rows expected = true := by
  cases selected : rows[index]? with
  | none => simp only [checkRowAt, selected, Bool.false_eq_true] at checked
  | some actual =>
      have accepted : decide
          (Compiler.canonical p actual.a = Compiler.canonical p expected.a ∧
           Compiler.canonical p actual.b = Compiler.canonical p expected.b) = true := by
        simpa only [checkRowAt, selected] using checked
      exact List.any_eq_true.mpr ⟨actual, List.mem_of_getElem? selected, accepted⟩

inductive ProductData where
  | foldedLeft (coefficient : Int)
  | foldedRight (coefficient : Int)
  | square (row : Nat)
  | product (minus plus : Nat) (auxiliary : Linear)

def ProductData.ordinary : ProductData → ScalarRows.ProductData
  | .foldedLeft coefficient => .foldedLeft coefficient
  | .foldedRight coefficient => .foldedRight coefficient
  | .square _ => .square
  | .product _ _ auxiliary => .product auxiliary

def checkProduct (p : Nat) (rows : List Row) (left right output : Linear) : ProductData → Bool
  | .foldedLeft coefficient => ScalarRows.checkProduct p rows left right output (.foldedLeft coefficient)
  | .foldedRight coefficient => ScalarRows.checkProduct p rows left right output (.foldedRight coefficient)
  | .square row => decide (Compiler.canonical p left = Compiler.canonical p right) &&
      checkRowAt p rows row ⟨left, output⟩
  | .product minus plus auxiliary =>
      checkRowAt p rows minus ⟨Compiler.subtract left right, auxiliary⟩ &&
      checkRowAt p rows plus ⟨left ++ right, auxiliary ++ scaleLinear 4 output⟩

theorem checked_product_membership (p : Nat) (rows : List Row)
    (left right output : Linear) (data : ProductData)
    (checked : checkProduct p rows left right output data = true) :
    ScalarRows.checkProduct p rows left right output data.ordinary = true := by
  cases data with
  | foldedLeft coefficient => exact checked
  | foldedRight coefficient => exact checked
  | square row =>
      simp only [checkProduct, Bool.and_eq_true] at checked
      simp only [ScalarRows.checkProduct, ProductData.ordinary, Bool.and_eq_true]
      exact ⟨checked.1,
        checked_row_membership p rows row ⟨left, output⟩ checked.2⟩
  | product minus plus auxiliary =>
      simp only [checkProduct, Bool.and_eq_true] at checked
      simp only [ScalarRows.checkProduct, ProductData.ordinary, Bool.and_eq_true]
      exact
        ⟨checked_row_membership p rows minus ⟨Compiler.subtract left right, auxiliary⟩ checked.1,
         checked_row_membership p rows plus ⟨left ++ right, auxiliary ++ scaleLinear 4 output⟩ checked.2⟩

structure StepData where
  before : Linear
  left : Linear
  after : Linear
  right : Bool
  factor : Linear
  target : Linear
  product : ProductData

def StepData.ordinary (step : StepData) : ScalarRows.StepData where
  before := step.before
  left := step.left
  after := step.after
  right := step.right
  factor := step.factor
  target := step.target
  product := step.product.ordinary

def checkStep (p : Nat) (rows : List Row) (step : StepData) : Bool :=
  decide (Compiler.canonical p step.factor = Compiler.canonical p (ScalarRows.factor step.ordinary) ∧
    Compiler.canonical p step.target = Compiler.canonical p (ScalarRows.target step.ordinary)) &&
  checkProduct p rows step.before step.factor step.target step.product

theorem checked_step_membership (p : Nat) (rows : List Row) (step : StepData)
    (checked : checkStep p rows step = true) :
    ScalarRows.checkStep p rows step.ordinary = true := by
  simp only [checkStep, Bool.and_eq_true] at checked
  simp only [ScalarRows.checkStep, Bool.and_eq_true]
  exact ⟨checked.1,
    checked_product_membership p rows step.before step.factor step.target step.product checked.2⟩

def checkChain (p : Nat) (rows : List Row) : Linear → List StepData → Bool
  | _, [] => true
  | previous, step :: tail =>
      (decide (Compiler.canonical p step.before = Compiler.canonical p previous) &&
        checkStep p rows step) && checkChain p rows step.after tail

/-- Symbolic conversion proves every indexed row is a member of the SAME raw
relation subset. Existing arbitrary-assignment chain semantics are reused; row
indices add evidence about location, never a multiplication/ordering premise. -/
theorem checked_chain_membership (p : Nat) (rows : List Row)
    (previous : Linear) (steps : List StepData)
    (checked : checkChain p rows previous steps = true) :
    ScalarRows.checkChain p rows previous (steps.map StepData.ordinary) = true := by
  induction steps generalizing previous with
  | nil => rfl
  | cons step tail ih =>
      simp only [checkChain, Bool.and_eq_true] at checked
      simp only [List.map_cons, ScalarRows.checkChain, Bool.and_eq_true]
      exact
        ⟨⟨checked.1.1, checked_step_membership p rows step checked.1.2⟩,
         ih step.after checked.2⟩


end ShielddSecurity.ScalarIndexed
set_option pp.all true in
#check @ShielddSecurity.ScalarIndexed.checked_row_membership
#print axioms ShielddSecurity.ScalarIndexed.checked_row_membership

set_option pp.all true in
#check @ShielddSecurity.ScalarIndexed.checked_product_membership
#print axioms ShielddSecurity.ScalarIndexed.checked_product_membership

set_option pp.all true in
#check @ShielddSecurity.ScalarIndexed.checked_step_membership
#print axioms ShielddSecurity.ScalarIndexed.checked_step_membership

set_option pp.all true in
#check @ShielddSecurity.ScalarIndexed.checked_chain_membership
#print axioms ShielddSecurity.ScalarIndexed.checked_chain_membership
