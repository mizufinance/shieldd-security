-- GENERATED from rows.json by generate.py. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAuthorizationAdd509
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def rows0 : List Row := [⟨[(1980,1),(4269,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64441,1)]⟩,⟨[(1980,1),(4269,1)],[(64440,4),(64441,1)]⟩]
theorem actual0 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41702 2 rows0=true := by decide +kernel
theorem checked0 : (checkRow p rows0 ⟨subtract [(1980,1)] [(4269,1)],[(64441,1)]⟩ &&
  checkRow p rows0 ⟨[(1980,1)]++[(4269,1)],[(64441,1)]++scaleLinear 4 [(64440,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value0 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64440=rho 1980*rho 4269 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41702 2 rows0 actual0 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked0
  have result := checked_product_sound rho rows0 [(1980,1)] [(4269,1)] [(64440,1)] [(64441,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows1 : List Row := [⟨[(1981,1),(4270,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64443,1)]⟩,⟨[(1981,1),(4270,1)],[(64442,4),(64443,1)]⟩]
theorem actual1 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41704 2 rows1=true := by decide +kernel
theorem checked1 : (checkRow p rows1 ⟨subtract [(1981,1)] [(4270,1)],[(64443,1)]⟩ &&
  checkRow p rows1 ⟨[(1981,1)]++[(4270,1)],[(64443,1)]++scaleLinear 4 [(64442,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value1 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64442=rho 1981*rho 4270 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41704 2 rows1 actual1 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked1
  have result := checked_product_sound rho rows1 [(1981,1)] [(4270,1)] [(64442,1)] [(64443,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows2 : List Row := [⟨[(64440,1),(64442,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64445,1)]⟩,⟨[(64440,1),(64442,1)],[(64444,4),(64445,1)]⟩]
theorem actual2 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41706 2 rows2=true := by decide +kernel
theorem checked2 : (checkRow p rows2 ⟨subtract [(64440,1)] [(64442,1)],[(64445,1)]⟩ &&
  checkRow p rows2 ⟨[(64440,1)]++[(64442,1)],[(64445,1)]++scaleLinear 4 [(64444,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value2 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64444=rho 64440*rho 64442 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41706 2 rows2 actual2 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked2
  have result := checked_product_sound rho rows2 [(64440,1)] [(64442,1)] [(64444,1)] [(64445,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows3 : List Row := [⟨[(64444,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(64447,1)]⟩,⟨[(200692,2)],[(64446,4),(64447,1)]⟩]
theorem actual3 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41708 2 rows3=true := by decide +kernel
theorem checked3 : (checkRow p rows3 ⟨subtract [(copy,1),(64444,CapturedFirstSubgroup81.d)] [(copy,1),(64444,-CapturedFirstSubgroup81.d)],[(64447,1)]⟩ &&
  checkRow p rows3 ⟨[(copy,1),(64444,CapturedFirstSubgroup81.d)]++[(copy,1),(64444,-CapturedFirstSubgroup81.d)],[(64447,1)]++scaleLinear 4 [(64446,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value3 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64446=(1+(CapturedFirstSubgroup81.d:F)*rho 64444)*(1-(CapturedFirstSubgroup81.d:F)*rho 64444) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41708 2 rows3 actual3 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked3
  have result := checked_product_sound rho rows3 [(copy,1),(64444,CapturedFirstSubgroup81.d)] [(copy,1),(64444,-CapturedFirstSubgroup81.d)] [(64446,1)] [(64447,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows4 : List Row := [⟨[(4271,1),(64446,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64449,1)]⟩,⟨[(4271,1),(64446,1)],[(64448,4),(64449,1)]⟩]
theorem actual4 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41710 2 rows4=true := by decide +kernel
theorem checked4 : (checkRow p rows4 ⟨subtract [(4271,1)] [(64446,1)],[(64449,1)]⟩ &&
  checkRow p rows4 ⟨[(4271,1)]++[(64446,1)],[(64449,1)]++scaleLinear 4 [(64448,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value4 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64448=rho 4271*rho 64446 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41710 2 rows4 actual4 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked4
  have result := checked_product_sound rho rows4 [(4271,1)] [(64446,1)] [(64448,1)] [(64449,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows5 : List Row := [⟨[(1980,1),(4270,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64451,1)]⟩,⟨[(1980,1),(4270,1)],[(64450,4),(64451,1)]⟩]
theorem actual5 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41712 2 rows5=true := by decide +kernel
theorem checked5 : (checkRow p rows5 ⟨subtract [(1980,1)] [(4270,1)],[(64451,1)]⟩ &&
  checkRow p rows5 ⟨[(1980,1)]++[(4270,1)],[(64451,1)]++scaleLinear 4 [(64450,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value5 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64450=rho 1980*rho 4270 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41712 2 rows5 actual5 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked5
  have result := checked_product_sound rho rows5 [(1980,1)] [(4270,1)] [(64450,1)] [(64451,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows6 : List Row := [⟨[(1981,1),(4269,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64453,1)]⟩,⟨[(1981,1),(4269,1)],[(64452,4),(64453,1)]⟩]
theorem actual6 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41714 2 rows6=true := by decide +kernel
theorem checked6 : (checkRow p rows6 ⟨subtract [(1981,1)] [(4269,1)],[(64453,1)]⟩ &&
  checkRow p rows6 ⟨[(1981,1)]++[(4269,1)],[(64453,1)]++scaleLinear 4 [(64452,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value6 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64452=rho 1981*rho 4269 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41714 2 rows6 actual6 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked6
  have result := checked_product_sound rho rows6 [(1981,1)] [(4269,1)] [(64452,1)] [(64453,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows7 : List Row := [⟨[(64444,19257038036680949359750312669786877991949435402254120286184196891950884077233),(64450,1),(64452,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64455,1)]⟩,⟨[(64444,33178837138445241119697427838399087845741117098273517536419461807987697107280),(64450,1),(64452,1),(200692,1)],[(64454,4),(64455,1)]⟩]
theorem actual7 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41716 2 rows7=true := by decide +kernel
theorem checked7 : (checkRow p rows7 ⟨subtract [(64450,1),(64452,1)] [(copy,1),(64444,-CapturedFirstSubgroup81.d)],[(64455,1)]⟩ &&
  checkRow p rows7 ⟨[(64450,1),(64452,1)]++[(copy,1),(64444,-CapturedFirstSubgroup81.d)],[(64455,1)]++scaleLinear 4 [(64454,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value7 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64454=(rho 64450+rho 64452)*(1-(CapturedFirstSubgroup81.d:F)*rho 64444) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41716 2 rows7 actual7 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked7
  have result := checked_product_sound rho rows7 [(64450,1),(64452,1)] [(copy,1),(64444,-CapturedFirstSubgroup81.d)] [(64454,1)] [(64455,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows8 : List Row := [⟨[(4271,52435875175126190479447740508185965837690552500527637822603658699938581184512),(64454,1)],[(64457,1)]⟩,⟨[(4271,1),(64454,1)],[(64456,4),(64457,1)]⟩]
theorem actual8 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41718 2 rows8=true := by decide +kernel
theorem checked8 : (checkRow p rows8 ⟨subtract [(64454,1)] [(4271,1)],[(64457,1)]⟩ &&
  checkRow p rows8 ⟨[(64454,1)]++[(4271,1)],[(64457,1)]++scaleLinear 4 [(64456,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value8 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64456=rho 64454*rho 4271 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41718 2 rows8 actual8 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked8
  have result := checked_product_sound rho rows8 [(64454,1)] [(4271,1)] [(64456,1)] [(64457,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows9 : List Row := [⟨[(64440,1),(64442,1),(64444,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(64459,1)]⟩,⟨[(64440,1),(64442,1),(64444,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(64458,4),(64459,1)]⟩]
theorem actual9 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41720 2 rows9=true := by decide +kernel
theorem checked9 : (checkRow p rows9 ⟨subtract [(64440,1),(64442,1)] [(copy,1),(64444,CapturedFirstSubgroup81.d)],[(64459,1)]⟩ &&
  checkRow p rows9 ⟨[(64440,1),(64442,1)]++[(copy,1),(64444,CapturedFirstSubgroup81.d)],[(64459,1)]++scaleLinear 4 [(64458,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value9 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64458=(rho 64440+rho 64442)*(1+(CapturedFirstSubgroup81.d:F)*rho 64444) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41720 2 rows9 actual9 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked9
  have result := checked_product_sound rho rows9 [(64440,1),(64442,1)] [(copy,1),(64444,CapturedFirstSubgroup81.d)] [(64458,1)] [(64459,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows10 : List Row := [⟨[(4271,52435875175126190479447740508185965837690552500527637822603658699938581184512),(64458,1)],[(64461,1)]⟩,⟨[(4271,1),(64458,1)],[(64460,4),(64461,1)]⟩]
theorem actual10 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 41722 2 rows10=true := by decide +kernel
theorem checked10 : (checkRow p rows10 ⟨subtract [(64458,1)] [(4271,1)],[(64461,1)]⟩ &&
  checkRow p rows10 ⟨[(64458,1)]++[(4271,1)],[(64461,1)]++scaleLinear 4 [(64460,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value10 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 64460=rho 64458*rho 4271 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 41722 2 rows10 actual10 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked10
  have result := checked_product_sound rho rows10 [(64458,1)] [(4271,1)] [(64460,1)] [(64461,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
variable {F : Type} [Field F] [CharP F p]
theorem values (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    let left := VariableWindowColumns449.columnPoint rho 1980
    let right := VariableWindowColumns449.columnPoint rho 4269
    let dt := Group.delta (CapturedFirstSubgroup81.d:F) left right
    rho 64448=rho 4271*((1+dt)*(1-dt)) ∧
    rho 64456=Group.cross left right*(1-dt)*rho 4271 ∧
    rho 64460=Group.diagonal left right*(1+dt)*rho 4271 := by
  dsimp only
  have v10 := value10 rho one arithmetic
  have v9 := value9 rho one arithmetic
  have v8 := value8 rho one arithmetic
  have v7 := value7 rho one arithmetic
  have v6 := value6 rho one arithmetic
  have v5 := value5 rho one arithmetic
  have v4 := value4 rho one arithmetic
  have v3 := value3 rho one arithmetic
  have v2 := value2 rho one arithmetic
  have v1 := value1 rho one arithmetic
  have v0 := value0 rho one arithmetic
  rw [v10,v9,v8,v7,v6,v5,v4,v3,v2,v1,v0]
  simp only [VariableWindowColumns449.columnPoint,Group.delta,Group.cross,Group.diagonal]
  constructor
  · congr 2 <;> ring
  constructor <;> ring
def positions : List Nat := [4280,4288,4289]
def actualRows : List Row := [⟨[(64448,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[]⟩,⟨[(4272,52435875175126190479447740508185965837690552500527637822603658699938581184512),(64456,1)],[]⟩,⟨[(4273,52435875175126190479447740508185965837690552500527637822603658699938581184512),(64460,1)],[]⟩]
def templates : List Row :=
  [⟨subtract [(copy,1)] [(64448,1)],[]⟩,⟨subtract [(64456,1)] [(4272,1)],[]⟩,⟨subtract [(64460,1)] [(4273,1)],[]⟩]
theorem actual_checked : (List.range 3).all (fun i => decide
    (CapturedFullRelation58.rowAt (177954+positions.getD i 0)=actualRows[i]?))=true := by decide +kernel
theorem forward_checked : VariableOperationAdapter434.covers templates actualRows=true := by decide +kernel
theorem reverse_checked : VariableOperationAdapter434.covers actualRows templates=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+positions.getD i 0)) 3

theorem rows_iff (rho : Nat → F) (one : rho copy=1) : Rows rho ↔
    rho 64448=1 ∧ rho 64456=rho 4272 ∧ rho 64460=rho 4273 := by
  have actual : Rows rho ↔ Satisfies rho actualRows := by
    constructor
    · intro sat row member
      obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp member
      have bound : i<3 := (List.getElem?_eq_some_iff.mp found).1
      have check := of_decide_eq_true (List.all_eq_true.mp actual_checked i (List.mem_range.mpr bound))
      exact sat i bound row (check.trans found)
    · intro sat i bound row found
      have check := of_decide_eq_true (List.all_eq_true.mp actual_checked i (List.mem_range.mpr bound))
      exact sat row (List.mem_iff_getElem?.mpr ⟨i,check.symm.trans found⟩)
  rw [actual]
  have equivalent : Satisfies rho actualRows ↔ Satisfies rho templates :=
    ⟨transfer rho _ _ forward_checked,transfer rho _ _ reverse_checked⟩
  rw [equivalent]
  simp only [templates,Satisfies,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,VariableDoubleTemplate431.equality_row,eval,
    Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,←sub_eq_add_neg,sub_eq_zero]
  simp only [eq_comm]
end ShielddSecurity.CapturedAuthorizationAdd509

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows0
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows0

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual0
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual0

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked0
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked0

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value0
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value0

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows1
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows1

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual1
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual1

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked1
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked1

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value1
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value1

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows2
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows2

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual2
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual2

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked2
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked2

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value2
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value2

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows3
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows3

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual3
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual3

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked3
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked3

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value3
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value3

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows4
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows4

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual4
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual4

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked4
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked4

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value4
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value4

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows5
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows5

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual5
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual5

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked5
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked5

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value5
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value5

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows6
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows6

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual6
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual6

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked6
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked6

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value6
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value6

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows7
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows7

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual7
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual7

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked7
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked7

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value7
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value7

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows8
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows8

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual8
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual8

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked8
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked8

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value8
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value8

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows9
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows9

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual9
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual9

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked9
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked9

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value9
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value9

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows10
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows10

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual10
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual10

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.checked10
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.checked10

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.value10
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.value10

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.values
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.values

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.positions
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.positions

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actualRows
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actualRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.templates
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.templates

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.actual_checked
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.actual_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.forward_checked
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.forward_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.reverse_checked
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.reverse_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.Rows
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.Rows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationAdd509.rows_iff
#print axioms ShielddSecurity.CapturedAuthorizationAdd509.rows_iff
