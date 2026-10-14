import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionAdapter817
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01

def flagColumn (slot : Nat) : Nat := 19457+2*slot
def hintColumn (slot : Nat) : Nat := flagColumn slot+1
def inputColumn (slot : Nat) : Nat := if slot<33 then 19455 else 19456
def inverseOutput (slot : Nat) : Nat := 184129+4*slot
def zeroOutput (slot : Nat) : Nat := inverseOutput slot+2
def firstPosition (slot : Nat) : Nat := 19308+3*slot+slot/33
def deltaLinear (slot : Nat) : Linear := [(inputColumn slot,1),(copy,-((slot%33:Nat):Int))]
def inverseLinear (slot : Nat) : Linear := [(flagColumn slot,1),(inverseOutput slot,1),(copy,-1)]
structure Entry where
  slot : Nat
  inverse : MapArithmeticAdapter704.Entry
  zero : MapArithmeticAdapter704.Entry
  inverseRow : Row
  zeroRow : Row

def ProductShape (slot right output : Nat) (e : MapArithmeticAdapter704.Entry) : Prop :=
  e.square=false ∧ canonical p e.left=canonical p (deltaLinear slot) ∧
  e.right=[(right,1)] ∧ e.output=[(output,1)]
noncomputable instance productShapeDecidable (slot right output : Nat) (e : MapArithmeticAdapter704.Entry) :
    Decidable (ProductShape slot right output e) := by unfold ProductShape;infer_instance

def Valid (e : Entry) : Prop :=
  e.slot<66 ∧ MapArithmeticAdapter704.check e.inverse=true ∧ MapArithmeticAdapter704.check e.zero=true ∧
  ProductShape e.slot (hintColumn e.slot) (inverseOutput e.slot) e.inverse ∧
  ProductShape e.slot (flagColumn e.slot) (zeroOutput e.slot) e.zero ∧
  CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+firstPosition e.slot) 1 [e.inverseRow]=true ∧
  CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+firstPosition e.slot+1) 1 [e.zeroRow]=true ∧
  canonical p e.inverseRow.a=canonical p (inverseLinear e.slot) ∧
  canonical p e.inverseRow.b=canonical p [] ∧
  canonical p e.zeroRow.a=canonical p [(zeroOutput e.slot,-1)] ∧ canonical p e.zeroRow.b=canonical p []
noncomputable instance validDecidable (e : Entry) : Decidable (Valid e) := by unfold Valid;infer_instance
noncomputable def check (e : Entry) : Bool := decide (Valid e)

theorem valid (e : Entry) (checked : check e=true) : Valid e := of_decide_eq_true checked

theorem product_equation (slot right output : Nat) (e : MapArithmeticAdapter704.Entry)
    (checked : MapArithmeticAdapter704.check e=true) (shape : ProductShape slot right output e)
    (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho output=(rho (inputColumn slot)-((slot%33:Nat):F))*rho right := by
  have equation := MapArithmeticAdapter704.equation e checked rho arithmetic
  rcases shape with ⟨square,left,rightShape,outputShape⟩
  rw [square,outputShape,rightShape,canonical_equal rho _ _ left] at equation
  simpa only [Bool.false_eq_true,if_false,deltaLinear,eval,Int.cast_one,one_mul,Int.cast_neg,
    Int.cast_natCast,add_zero,one,mul_one,neg_mul,sub_eq_add_neg] using equation

theorem equations (e : Entry) (checked : check e=true) (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho (inverseOutput e.slot)=(rho (inputColumn e.slot)-((e.slot%33:Nat):F))*rho (hintColumn e.slot) ∧
    rho (zeroOutput e.slot)=(rho (inputColumn e.slot)-((e.slot%33:Nat):F))*rho (flagColumn e.slot) := by
  have facts := valid e checked
  exact ⟨product_equation _ _ _ e.inverse facts.2.1 facts.2.2.2.1 rho one arithmetic,
    product_equation _ _ _ e.zero facts.2.2.1 facts.2.2.2.2.1 rho one arithmetic⟩

def Rows (rho : Nat → F) (slot : Nat) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+firstPosition slot+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+firstPosition slot+1+i)) 1

theorem rows (e : Entry) (checked : check e=true) (rho : Nat → F) (one : rho copy=1)
    (inverse : rho (inverseOutput e.slot)=1-rho (flagColumn e.slot)) (zero : rho (zeroOutput e.slot)=0) :
    Rows rho e.slot := by
  rcases valid e checked with ⟨_,_,_,_,_,capturedInverse,capturedZero,inverseA,inverseB,zeroA,zeroB⟩
  constructor
  · apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [e.inverseRow] capturedInverse rho).mp
    intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    unfold Square
    rw [canonical_equal rho _ _ inverseA,canonical_equal rho _ _ inverseB]
    simp only [inverseLinear,eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,one,inverse]
    ring
  · apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [e.zeroRow] capturedZero rho).mp
    intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    unfold Square
    rw [canonical_equal rho _ _ zeroA,canonical_equal rho _ _ zeroB]
    simp only [eval,zero,mul_zero,add_zero]
end ShielddSecurity.RoutingPrecisionAdapter817

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAdapter817.valid
#print axioms ShielddSecurity.RoutingPrecisionAdapter817.valid
set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAdapter817.product_equation
#print axioms ShielddSecurity.RoutingPrecisionAdapter817.product_equation
set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAdapter817.equations
#print axioms ShielddSecurity.RoutingPrecisionAdapter817.equations
set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAdapter817.Rows
#print axioms ShielddSecurity.RoutingPrecisionAdapter817.Rows
set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionAdapter817.rows
#print axioms ShielddSecurity.RoutingPrecisionAdapter817.rows
