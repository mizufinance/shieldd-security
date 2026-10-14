import ShielddSecurity.RoutingSelectorAlgebra821
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingSelectorAdapter822
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
open RoutingSelectorAlgebra821 (suffix flags)

def orderOutput (index : Nat) : Nat := 184393+2*index
def activeOutput (index : Nat) : Nat := 184865+2*index
def activeLinear (index : Nat) : Linear := suffix 19523 index++[(activeOutput index,1)]
structure Entry where
  index : Nat
  order : MapArithmeticAdapter704.Entry
  active : MapArithmeticAdapter704.Entry
  orderRow : Row
  activeRow : Row

def ProductShape (left right : Linear) (output : Nat) (e : MapArithmeticAdapter704.Entry) : Prop :=
  e.square=false ∧ canonical p e.left=canonical p left ∧ canonical p e.right=canonical p right ∧
  e.output=[(output,1)]
noncomputable instance productShapeDecidable (left right : Linear) (output : Nat) (e : MapArithmeticAdapter704.Entry) :
    Decidable (ProductShape left right output e) := by unfold ProductShape;infer_instance

def Valid (e : Entry) : Prop :=
  e.index<32 ∧ MapArithmeticAdapter704.check e.order=true ∧ MapArithmeticAdapter704.check e.active=true ∧
  ProductShape (suffix 19457 e.index) (subtract [(copy,1)] (suffix 19523 e.index)) (orderOutput e.index) e.order ∧
  ProductShape [(10,1)] (subtract (suffix 19457 e.index) (suffix 19523 e.index)) (activeOutput e.index) e.active ∧
  CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+19507+e.index) 1 [e.orderRow]=true ∧
  CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+19540+e.index) 1 [e.activeRow]=true ∧
  canonical p e.orderRow.a=canonical p [(orderOutput e.index,-1)] ∧ canonical p e.orderRow.b=canonical p [] ∧
  canonical p e.activeRow.a=canonical p (activeLinear e.index) ∧ canonical p e.activeRow.b=canonical p (activeLinear e.index)
noncomputable instance validDecidable (e : Entry) : Decidable (Valid e) := by unfold Valid;infer_instance
noncomputable def check (e : Entry) : Bool := decide (Valid e)
theorem valid (e : Entry) (checked : check e=true) : Valid e := of_decide_eq_true checked

theorem product_equation (left right : Linear) (output : Nat) (e : MapArithmeticAdapter704.Entry)
    (checked : MapArithmeticAdapter704.check e=true) (shape : ProductShape left right output e)
    (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho output=eval rho left*eval rho right := by
  have equation := MapArithmeticAdapter704.equation e checked rho arithmetic
  rcases shape with ⟨square,leftShape,rightShape,outputShape⟩
  rw [square,outputShape,canonical_equal rho _ _ leftShape,canonical_equal rho _ _ rightShape] at equation
  simpa only [Bool.false_eq_true,if_false,eval,Int.cast_one,one_mul,add_zero] using equation

theorem equations (e : Entry) (checked : check e=true) (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho (orderOutput e.index)=eval rho (suffix 19457 e.index)*(1-eval rho (suffix 19523 e.index)) ∧
    rho (activeOutput e.index)=rho 10*(eval rho (suffix 19457 e.index)-eval rho (suffix 19523 e.index)) := by
  have facts := valid e checked
  have order := product_equation _ _ _ e.order facts.2.1 facts.2.2.2.1 rho arithmetic
  have active := product_equation _ _ _ e.active facts.2.2.1 facts.2.2.2.2.1 rho arithmetic
  constructor
  · simpa only [eval_subtract,eval,Int.cast_one,one_mul,add_zero,one] using order
  · simpa only [eval_subtract,eval,Int.cast_one,one_mul,add_zero] using active

def Rows (rho : Nat → F) (index : Nat) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19507+index+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19540+index+i)) 1

theorem rows (e : Entry) (checked : check e=true) (rho : Nat → F)
    (order : rho (orderOutput e.index)=0)
    (active : let value := eval rho (suffix 19523 e.index)+rho (activeOutput e.index);value*value=value) :
    Rows rho e.index := by
  rcases valid e checked with ⟨_,_,_,_,_,capturedOrder,capturedActive,orderA,orderB,activeA,activeB⟩
  constructor
  · apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [e.orderRow] capturedOrder rho).mp
    intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    unfold Square
    rw [canonical_equal rho _ _ orderA,canonical_equal rho _ _ orderB]
    simp only [eval,order,mul_zero,add_zero]
  · apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [e.activeRow] capturedActive rho).mp
    intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    unfold Square
    rw [canonical_equal rho _ _ activeA,canonical_equal rho _ _ activeB]
    simpa only [activeLinear,eval_append,eval,Int.cast_one,one_mul,add_zero] using active

theorem sum_row (position start : Nat) (row : Row)
    (captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+position) 1 [row]=true)
    (left : canonical p row.a=canonical p (subtract [(copy,1)] (flags start (List.range 33))))
    (right : canonical p row.b=canonical p []) (rho : Nat → F) (one : rho copy=1)
    (sum : eval rho (flags start (List.range 33))=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+position+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row] captured rho).mp
  intro actual member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst actual
  unfold Square
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right,eval_subtract,sum]
  simp only [eval,Int.cast_one,one_mul,add_zero,one,sub_self,mul_zero]
end ShielddSecurity.RoutingSelectorAdapter822

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAdapter822.valid
#print axioms ShielddSecurity.RoutingSelectorAdapter822.valid
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAdapter822.product_equation
#print axioms ShielddSecurity.RoutingSelectorAdapter822.product_equation
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAdapter822.equations
#print axioms ShielddSecurity.RoutingSelectorAdapter822.equations
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAdapter822.Rows
#print axioms ShielddSecurity.RoutingSelectorAdapter822.Rows
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAdapter822.rows
#print axioms ShielddSecurity.RoutingSelectorAdapter822.rows
set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorAdapter822.sum_row
#print axioms ShielddSecurity.RoutingSelectorAdapter822.sum_row
