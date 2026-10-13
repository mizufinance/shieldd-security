import ShielddSecurity.VariableSelectorAdapter437
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedSelectorAdapter480
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
structure Entry where
  low : Nat
  high : Nat
  bx : Int
  by_ : Int
  tx : Int
  ty : Int
  ux : Int
  uy : Int
  productX : Nat
  productY : Nat
  arithmeticStart : Nat
  arithmeticRows : List Row
  outputX : Linear
  outputY : Linear

def rightX (e : Entry) : Linear := [(copy,e.tx),(e.low,e.ux-e.tx-e.bx)]
def rightY (e : Entry) : Linear := [(copy,e.ty-1),(e.low,e.uy-e.ty-e.by_+1)]
def expectedX (e : Entry) : Linear := [(e.low,e.bx),(e.productX,1)]
def expectedY (e : Entry) : Linear := [(copy,1),(e.low,e.by_-1),(e.productY,1)]
noncomputable def productCheck (e : Entry) (terms : Linear) (output : Nat) : Bool :=
  checkRow p e.arithmeticRows ⟨subtract [(e.high,1)] terms,[(output+1,1)]⟩ &&
  checkRow p e.arithmeticRows ⟨[(e.high,1)]++terms,[(output+1,1)]++scaleLinear 4 [(output,1)]⟩
def Valid (e : Entry) : Prop :=
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt e.arithmeticStart e.arithmeticRows.length e.arithmeticRows=true ∧
  e.arithmeticStart+e.arithmeticRows.length≤177954 ∧
  productCheck e (rightX e) e.productX=true ∧ productCheck e (rightY e) e.productY=true ∧
  canonical p e.outputX=canonical p (expectedX e) ∧ canonical p e.outputY=canonical p (expectedY e)
noncomputable instance validDecidable (e : Entry) : Decidable (Valid e) := by
  unfold Valid
  infer_instance
noncomputable def check (e : Entry) : Bool := decide (Valid e)

def base {F : Type} [Field F] (e : Entry) : Group.Point F := ⟨(e.bx:F),(e.by_:F)⟩
def twice {F : Type} [Field F] (e : Entry) : Group.Point F := ⟨(e.tx:F),(e.ty:F)⟩
def triple {F : Type} [Field F] (e : Entry) : Group.Point F := ⟨(e.ux:F),(e.uy:F)⟩
variable {F : Type} [Field F] [CharP F p]
theorem product (e : Entry) (terms : Linear) (output : Nat) (checked : productCheck e terms output=true)
    (rho : Nat → F) (sat : Satisfies rho e.arithmeticRows) : rho output=rho e.high*eval rho terms := by
  have checks := Bool.and_eq_true_iff.mp checked
  have result := checked_product_sound rho e.arithmeticRows [(e.high,1)] terms [(output,1)] [(output+1,1)]
    four_ne_zero sat checks.1 checks.2
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result

theorem coordinates (e : Entry) (checked : check e=true) (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Group.Point.mk (eval rho e.outputX) (eval rho e.outputY)=
      Group.windowPoint (rho e.low) (rho e.high) (base e) (twice e) (triple e) := by
  have valid : Valid e := of_decide_eq_true checked
  rcases valid with ⟨actual,inside,xcheck,ycheck,x,y⟩
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954
    e.arithmeticStart e.arithmeticRows.length e.arithmeticRows actual inside rho arithmetic
  have px := product e (rightX e) e.productX xcheck rho sat
  have py := product e (rightY e) e.productY ycheck rho sat
  rw [canonical_equal rho e.outputX (expectedX e) x,canonical_equal rho e.outputY (expectedY e) y]
  simp only [expectedX,expectedY,eval,Int.cast_one,Int.cast_sub,one_mul,mul_one,add_zero,one,
    px,py,rightX,rightY,eval,Int.cast_add,Int.cast_sub,Int.cast_one,mul_one,add_zero,one,
    base,twice,triple,Group.windowPoint,Group.chooseCoordinate]
  congr 1 <;> ring
end ShielddSecurity.FixedSelectorAdapter480

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.Entry
#print axioms ShielddSecurity.FixedSelectorAdapter480.Entry

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.rightX
#print axioms ShielddSecurity.FixedSelectorAdapter480.rightX

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.rightY
#print axioms ShielddSecurity.FixedSelectorAdapter480.rightY

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.expectedX
#print axioms ShielddSecurity.FixedSelectorAdapter480.expectedX

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.expectedY
#print axioms ShielddSecurity.FixedSelectorAdapter480.expectedY

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.productCheck
#print axioms ShielddSecurity.FixedSelectorAdapter480.productCheck

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.Valid
#print axioms ShielddSecurity.FixedSelectorAdapter480.Valid

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.check
#print axioms ShielddSecurity.FixedSelectorAdapter480.check

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.base
#print axioms ShielddSecurity.FixedSelectorAdapter480.base

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.twice
#print axioms ShielddSecurity.FixedSelectorAdapter480.twice

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.triple
#print axioms ShielddSecurity.FixedSelectorAdapter480.triple

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.product
#print axioms ShielddSecurity.FixedSelectorAdapter480.product

set_option pp.all true in
#check @ShielddSecurity.FixedSelectorAdapter480.coordinates
#print axioms ShielddSecurity.FixedSelectorAdapter480.coordinates
