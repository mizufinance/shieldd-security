-- GENERATED from rows.json; do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignCapture654
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def productRows : List Row := [⟨[(21711,1),(21712,2)],[(190246,1)]⟩,⟨[(21711,1),(21712,52435875175126190479447740508185965837690552500527637822603658699938581184511)],[(190245,4),(190246,1)]⟩]
noncomputable def assertionRows : List Row := [⟨[(4281,1),(4534,1),(4789,52435875175126190479447740508185965837690552500527637822603658699938581184512),(6194,52435875175126190479447740508185965837690552500527637822603658699938581184512),(21712,52435875175126190479447740508185965837690552500527637822603658699938581184512),(190245,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
noncomputable def template : List Row :=
  [⟨subtract [(4281,1),(4534,1),(4789,-1),(6194,-1)] [(21712,1),(190245,1)],[]⟩]
theorem product_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 167507 2 productRows=true := by decide +kernel
theorem assertion_checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt 199867 1 assertionRows=true := by decide +kernel
theorem shape_checked : VariableOperationAdapter434.covers template assertionRows=true ∧
    VariableOperationAdapter434.covers assertionRows template=true := by constructor <;> decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem product (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190245=rho 21711*(-2*rho 21712) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 167507 2 productRows product_checked (by decide) rho arithmetic
  have result := checked_product_sound rho productRows [(21711,1)] [(21712,-2)]
    [(190245,1)] [(190246,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero] using result

theorem rows_iff (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (199867+i)) 1 ↔
    rho 4281+rho 4534-rho 4789-rho 6194=(1-2*rho 21711)*rho 21712 := by
  have shapes : Satisfies rho assertionRows ↔ Satisfies rho template :=
    ⟨transfer rho _ _ shape_checked.1,
      transfer rho _ _ shape_checked.2⟩
  rw [←CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 199867 1 assertionRows assertion_checked rho,shapes]
  simp only [template,Satisfies,List.mem_singleton,forall_eq,VariableDoubleTemplate431.equality_row,
    eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul]
  rw [product rho arithmetic]
  ring_nf
end ShielddSecurity.BalanceSignCapture654

set_option pp.all true in
#check @ShielddSecurity.BalanceSignCapture654.product_checked
#print axioms ShielddSecurity.BalanceSignCapture654.product_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceSignCapture654.assertion_checked
#print axioms ShielddSecurity.BalanceSignCapture654.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceSignCapture654.shape_checked
#print axioms ShielddSecurity.BalanceSignCapture654.shape_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceSignCapture654.product
#print axioms ShielddSecurity.BalanceSignCapture654.product

set_option pp.all true in
#check @ShielddSecurity.BalanceSignCapture654.rows_iff
#print axioms ShielddSecurity.BalanceSignCapture654.rows_iff
