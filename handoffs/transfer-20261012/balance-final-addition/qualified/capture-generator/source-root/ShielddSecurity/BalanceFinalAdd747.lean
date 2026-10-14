-- GENERATED from rows.json by generate.py. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalAdd747
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def rows0 : List Row := [⟨[(22230,1),(22734,52435875175126190479447740508185965837690552500527637822603658699938581184512),(192706,1)],[(195215,1)]⟩,⟨[(22230,1),(22734,1),(192706,1)],[(195214,4),(195215,1)]⟩]
theorem actual0 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172476 2 rows0=true := by decide +kernel
theorem checked0 : (checkRow p rows0 ⟨subtract [(22230,1),(192706,1)] [(22734,1)],[(195215,1)]⟩ &&
  checkRow p rows0 ⟨[(22230,1),(192706,1)]++[(22734,1)],[(195215,1)]++scaleLinear 4 [(195214,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value0 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195214=(rho 22230+rho 192706)*rho 22734 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172476 2 rows0 actual0 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked0
  have result := checked_product_sound rho rows0 [(22230,1),(192706,1)] [(22734,1)] [(195214,1)] [(195215,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows1 : List Row := [⟨[(22231,1),(22735,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(195217,1)]⟩,⟨[(22231,1),(22735,1)],[(195216,4),(195217,1)]⟩]
theorem actual1 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172478 2 rows1=true := by decide +kernel
theorem checked1 : (checkRow p rows1 ⟨subtract [(22231,1)] [(22735,1)],[(195217,1)]⟩ &&
  checkRow p rows1 ⟨[(22231,1)]++[(22735,1)],[(195217,1)]++scaleLinear 4 [(195216,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value1 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195216=rho 22231*rho 22735 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172478 2 rows1 actual1 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked1
  have result := checked_product_sound rho rows1 [(22231,1)] [(22735,1)] [(195216,1)] [(195217,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows2 : List Row := [⟨[(195214,1),(195216,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(195219,1)]⟩,⟨[(195214,1),(195216,1)],[(195218,4),(195219,1)]⟩]
theorem actual2 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172480 2 rows2=true := by decide +kernel
theorem checked2 : (checkRow p rows2 ⟨subtract [(195214,1)] [(195216,1)],[(195219,1)]⟩ &&
  checkRow p rows2 ⟨[(195214,1)]++[(195216,1)],[(195219,1)]++scaleLinear 4 [(195218,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value2 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195218=rho 195214*rho 195216 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172480 2 rows2 actual2 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked2
  have result := checked_product_sound rho rows2 [(195214,1)] [(195216,1)] [(195218,1)] [(195219,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows3 : List Row := [⟨[(195218,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(195221,1)]⟩,⟨[(200692,2)],[(195220,4),(195221,1)]⟩]
theorem actual3 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172482 2 rows3=true := by decide +kernel
theorem checked3 : (checkRow p rows3 ⟨subtract [(copy,1),(195218,CapturedFirstSubgroup81.d)] [(copy,1),(195218,-CapturedFirstSubgroup81.d)],[(195221,1)]⟩ &&
  checkRow p rows3 ⟨[(copy,1),(195218,CapturedFirstSubgroup81.d)]++[(copy,1),(195218,-CapturedFirstSubgroup81.d)],[(195221,1)]++scaleLinear 4 [(195220,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value3 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195220=(1+(CapturedFirstSubgroup81.d:F)*rho 195218)*(1-(CapturedFirstSubgroup81.d:F)*rho 195218) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172482 2 rows3 actual3 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked3
  have result := checked_product_sound rho rows3 [(copy,1),(195218,CapturedFirstSubgroup81.d)] [(copy,1),(195218,-CapturedFirstSubgroup81.d)] [(195220,1)] [(195221,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows4 : List Row := [⟨[(22736,1),(195220,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(195223,1)]⟩,⟨[(22736,1),(195220,1)],[(195222,4),(195223,1)]⟩]
theorem actual4 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172484 2 rows4=true := by decide +kernel
theorem checked4 : (checkRow p rows4 ⟨subtract [(22736,1)] [(195220,1)],[(195223,1)]⟩ &&
  checkRow p rows4 ⟨[(22736,1)]++[(195220,1)],[(195223,1)]++scaleLinear 4 [(195222,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value4 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195222=rho 22736*rho 195220 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172484 2 rows4 actual4 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked4
  have result := checked_product_sound rho rows4 [(22736,1)] [(195220,1)] [(195222,1)] [(195223,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows5 : List Row := [⟨[(22230,1),(22735,52435875175126190479447740508185965837690552500527637822603658699938581184512),(192706,1)],[(195225,1)]⟩,⟨[(22230,1),(22735,1),(192706,1)],[(195224,4),(195225,1)]⟩]
theorem actual5 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172486 2 rows5=true := by decide +kernel
theorem checked5 : (checkRow p rows5 ⟨subtract [(22230,1),(192706,1)] [(22735,1)],[(195225,1)]⟩ &&
  checkRow p rows5 ⟨[(22230,1),(192706,1)]++[(22735,1)],[(195225,1)]++scaleLinear 4 [(195224,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value5 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195224=(rho 22230+rho 192706)*rho 22735 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172486 2 rows5 actual5 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked5
  have result := checked_product_sound rho rows5 [(22230,1),(192706,1)] [(22735,1)] [(195224,1)] [(195225,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows6 : List Row := [⟨[(22231,1),(22734,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(195227,1)]⟩,⟨[(22231,1),(22734,1)],[(195226,4),(195227,1)]⟩]
theorem actual6 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172488 2 rows6=true := by decide +kernel
theorem checked6 : (checkRow p rows6 ⟨subtract [(22231,1)] [(22734,1)],[(195227,1)]⟩ &&
  checkRow p rows6 ⟨[(22231,1)]++[(22734,1)],[(195227,1)]++scaleLinear 4 [(195226,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value6 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195226=rho 22231*rho 22734 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172488 2 rows6 actual6 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked6
  have result := checked_product_sound rho rows6 [(22231,1)] [(22734,1)] [(195226,1)] [(195227,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows7 : List Row := [⟨[(195218,19257038036680949359750312669786877991949435402254120286184196891950884077233),(195224,1),(195226,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(195229,1)]⟩,⟨[(195218,33178837138445241119697427838399087845741117098273517536419461807987697107280),(195224,1),(195226,1),(200692,1)],[(195228,4),(195229,1)]⟩]
theorem actual7 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172490 2 rows7=true := by decide +kernel
theorem checked7 : (checkRow p rows7 ⟨subtract [(195224,1),(195226,1)] [(copy,1),(195218,-CapturedFirstSubgroup81.d)],[(195229,1)]⟩ &&
  checkRow p rows7 ⟨[(195224,1),(195226,1)]++[(copy,1),(195218,-CapturedFirstSubgroup81.d)],[(195229,1)]++scaleLinear 4 [(195228,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value7 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195228=(rho 195224+rho 195226)*(1-(CapturedFirstSubgroup81.d:F)*rho 195218) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172490 2 rows7 actual7 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked7
  have result := checked_product_sound rho rows7 [(195224,1),(195226,1)] [(copy,1),(195218,-CapturedFirstSubgroup81.d)] [(195228,1)] [(195229,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows8 : List Row := [⟨[(22736,52435875175126190479447740508185965837690552500527637822603658699938581184512),(195228,1)],[(195231,1)]⟩,⟨[(22736,1),(195228,1)],[(195230,4),(195231,1)]⟩]
theorem actual8 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172492 2 rows8=true := by decide +kernel
theorem checked8 : (checkRow p rows8 ⟨subtract [(195228,1)] [(22736,1)],[(195231,1)]⟩ &&
  checkRow p rows8 ⟨[(195228,1)]++[(22736,1)],[(195231,1)]++scaleLinear 4 [(195230,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value8 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195230=rho 195228*rho 22736 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172492 2 rows8 actual8 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked8
  have result := checked_product_sound rho rows8 [(195228,1)] [(22736,1)] [(195230,1)] [(195231,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows9 : List Row := [⟨[(195214,1),(195216,1),(195218,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(195233,1)]⟩,⟨[(195214,1),(195216,1),(195218,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(195232,4),(195233,1)]⟩]
theorem actual9 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172494 2 rows9=true := by decide +kernel
theorem checked9 : (checkRow p rows9 ⟨subtract [(195214,1),(195216,1)] [(copy,1),(195218,CapturedFirstSubgroup81.d)],[(195233,1)]⟩ &&
  checkRow p rows9 ⟨[(195214,1),(195216,1)]++[(copy,1),(195218,CapturedFirstSubgroup81.d)],[(195233,1)]++scaleLinear 4 [(195232,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value9 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195232=(rho 195214+rho 195216)*(1+(CapturedFirstSubgroup81.d:F)*rho 195218) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172494 2 rows9 actual9 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked9
  have result := checked_product_sound rho rows9 [(195214,1),(195216,1)] [(copy,1),(195218,CapturedFirstSubgroup81.d)] [(195232,1)] [(195233,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
def rows10 : List Row := [⟨[(22736,52435875175126190479447740508185965837690552500527637822603658699938581184512),(195232,1)],[(195235,1)]⟩,⟨[(22736,1),(195232,1)],[(195234,4),(195235,1)]⟩]
theorem actual10 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 172496 2 rows10=true := by decide +kernel
theorem checked10 : (checkRow p rows10 ⟨subtract [(195232,1)] [(22736,1)],[(195235,1)]⟩ &&
  checkRow p rows10 ⟨[(195232,1)]++[(22736,1)],[(195235,1)]++scaleLinear 4 [(195234,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem value10 (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 195234=rho 195232*rho 22736 := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 172496 2 rows10 actual10 (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp checked10
  have result := checked_product_sound rho rows10 [(195232,1)] [(22736,1)] [(195234,1)] [(195235,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,mul_one,add_zero,one,neg_mul,←sub_eq_add_neg] using result
variable {F : Type} [Field F] [CharP F p]
theorem values (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    let left := Group.Point.mk (rho 22230+rho 192706) (rho 22231)
    let right := VariableWindowColumns449.columnPoint rho 22734
    let dt := Group.delta (CapturedFirstSubgroup81.d:F) left right
    rho 195222=rho 22736*((1+dt)*(1-dt)) ∧
    rho 195230=Group.cross left right*(1-dt)*rho 22736 ∧
    rho 195234=Group.diagonal left right*(1+dt)*rho 22736 := by
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
def signRows : List Row := [⟨[(21711,1),(22230,2)],[(192707,1)]⟩,⟨[(21711,1),(22230,52435875175126190479447740508185965837690552500527637822603658699938581184511)],[(192706,4),(192707,1)]⟩]
theorem sign_actual : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 169968 2 signRows=true := by decide +kernel
theorem sign_checked : (checkRow p signRows ⟨subtract [(21711,1)] [(22230,-2)],[(192707,1)]⟩ &&
  checkRow p signRows ⟨[(21711,1)]++[(22230,-2)],[(192707,1)]++scaleLinear 4 [(192706,1)]⟩)=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p] in
theorem sign_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 192706=rho 21711*(-2*rho 22230) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 169968 2 signRows sign_actual (by decide) rho arithmetic
  have check := Bool.and_eq_true_iff.mp sign_checked
  have result := checked_product_sound rho signRows [(21711,1)] [(22230,-2)] [(192706,1)] [(192707,1)] four_ne_zero sat check.1 check.2
  simpa only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_mul] using result
def assertionRows : List Row := [⟨[(195222,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[]⟩]
theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+22811) 1 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 195222=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22811+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+22811) 1 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(195222,(p:Int)-1),(copy,1)]*eval rho [(195222,(p:Int)-1),(copy,1)]=eval rho []
  have shape : canonical p [(195222,(p:Int)-1),(copy,1)]=canonical p [(195222,-1),(copy,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]
end ShielddSecurity.BalanceFinalAdd747

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows0
#print axioms ShielddSecurity.BalanceFinalAdd747.rows0

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual0
#print axioms ShielddSecurity.BalanceFinalAdd747.actual0

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked0
#print axioms ShielddSecurity.BalanceFinalAdd747.checked0

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value0
#print axioms ShielddSecurity.BalanceFinalAdd747.value0

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows1
#print axioms ShielddSecurity.BalanceFinalAdd747.rows1

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual1
#print axioms ShielddSecurity.BalanceFinalAdd747.actual1

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked1
#print axioms ShielddSecurity.BalanceFinalAdd747.checked1

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value1
#print axioms ShielddSecurity.BalanceFinalAdd747.value1

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows2
#print axioms ShielddSecurity.BalanceFinalAdd747.rows2

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual2
#print axioms ShielddSecurity.BalanceFinalAdd747.actual2

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked2
#print axioms ShielddSecurity.BalanceFinalAdd747.checked2

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value2
#print axioms ShielddSecurity.BalanceFinalAdd747.value2

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows3
#print axioms ShielddSecurity.BalanceFinalAdd747.rows3

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual3
#print axioms ShielddSecurity.BalanceFinalAdd747.actual3

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked3
#print axioms ShielddSecurity.BalanceFinalAdd747.checked3

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value3
#print axioms ShielddSecurity.BalanceFinalAdd747.value3

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows4
#print axioms ShielddSecurity.BalanceFinalAdd747.rows4

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual4
#print axioms ShielddSecurity.BalanceFinalAdd747.actual4

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked4
#print axioms ShielddSecurity.BalanceFinalAdd747.checked4

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value4
#print axioms ShielddSecurity.BalanceFinalAdd747.value4

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows5
#print axioms ShielddSecurity.BalanceFinalAdd747.rows5

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual5
#print axioms ShielddSecurity.BalanceFinalAdd747.actual5

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked5
#print axioms ShielddSecurity.BalanceFinalAdd747.checked5

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value5
#print axioms ShielddSecurity.BalanceFinalAdd747.value5

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows6
#print axioms ShielddSecurity.BalanceFinalAdd747.rows6

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual6
#print axioms ShielddSecurity.BalanceFinalAdd747.actual6

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked6
#print axioms ShielddSecurity.BalanceFinalAdd747.checked6

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value6
#print axioms ShielddSecurity.BalanceFinalAdd747.value6

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows7
#print axioms ShielddSecurity.BalanceFinalAdd747.rows7

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual7
#print axioms ShielddSecurity.BalanceFinalAdd747.actual7

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked7
#print axioms ShielddSecurity.BalanceFinalAdd747.checked7

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value7
#print axioms ShielddSecurity.BalanceFinalAdd747.value7

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows8
#print axioms ShielddSecurity.BalanceFinalAdd747.rows8

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual8
#print axioms ShielddSecurity.BalanceFinalAdd747.actual8

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked8
#print axioms ShielddSecurity.BalanceFinalAdd747.checked8

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value8
#print axioms ShielddSecurity.BalanceFinalAdd747.value8

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows9
#print axioms ShielddSecurity.BalanceFinalAdd747.rows9

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual9
#print axioms ShielddSecurity.BalanceFinalAdd747.actual9

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked9
#print axioms ShielddSecurity.BalanceFinalAdd747.checked9

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value9
#print axioms ShielddSecurity.BalanceFinalAdd747.value9

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows10
#print axioms ShielddSecurity.BalanceFinalAdd747.rows10

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.actual10
#print axioms ShielddSecurity.BalanceFinalAdd747.actual10

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.checked10
#print axioms ShielddSecurity.BalanceFinalAdd747.checked10

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.value10
#print axioms ShielddSecurity.BalanceFinalAdd747.value10

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.values
#print axioms ShielddSecurity.BalanceFinalAdd747.values

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.signRows
#print axioms ShielddSecurity.BalanceFinalAdd747.signRows

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.sign_actual
#print axioms ShielddSecurity.BalanceFinalAdd747.sign_actual

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.sign_checked
#print axioms ShielddSecurity.BalanceFinalAdd747.sign_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.sign_value
#print axioms ShielddSecurity.BalanceFinalAdd747.sign_value

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.assertionRows
#print axioms ShielddSecurity.BalanceFinalAdd747.assertionRows

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.captured
#print axioms ShielddSecurity.BalanceFinalAdd747.captured

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalAdd747.rows
#print axioms ShielddSecurity.BalanceFinalAdd747.rows
