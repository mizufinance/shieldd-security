import ShielddSecurity.MapFirstCubic707
import ShielddSecurity.MapArithmeticCapture705B01
import ShielddSecurity.BalanceMapRoots700
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapRootRows708
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
open BalanceMapParameters699
open MapArithmeticCapture705B00

theorem qr_target (rho : Nat → F) (u : F)
    (flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0)
    (cubic : rho 189649=sourceFirstCubic u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    5*rho 189649+rho 189653=if BalanceMapRoots700.choice u then sourceFirstCubic u else 5*sourceFirstCubic u := by
  have raw := MapArithmeticAdapter704.equation entry5 checked5 rho arithmetic
  change eval rho entry5.output=eval rho entry5.left*eval rho entry5.right at raw
  have out : eval rho entry5.output=rho 189653 := by simp only [entry5,eval,Int.cast_one,one_mul,add_zero]
  have left : eval rho entry5.left=rho 20935 := by simp only [entry5,eval,Int.cast_one,one_mul,add_zero]
  have shape : canonical p entry5.right=canonical p (subtract [(189649,1)] [(189649,5)]) := by decide +kernel
  have right : eval rho entry5.right=rho 189649-5*rho 189649 := by
    rw [canonical_equal rho _ _ shape,eval_subtract]
    simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat]
  rw [out,left,right,flag,cubic] at raw
  rw [cubic]
  cases h : BalanceMapRoots700.choice u <;> simp only [h,Bool.false_eq_true,if_false,if_true,zero_mul,one_mul] at raw ⊢ <;> linear_combination raw

theorem alternative_value (rho : Nat → F) (u : F)
    (q : rho 189643=5*u*u) (cubic : rho 189649=sourceFirstCubic u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 189651=5*u*u*sourceFirstCubic u := by
  have raw := MapArithmeticAdapter704.equation entry4 checked4 rho arithmetic
  change eval rho entry4.output=eval rho entry4.left*eval rho entry4.right at raw
  simpa only [entry4,eval,Int.cast_one,one_mul,add_zero,q,cubic] using raw

theorem y_target (rho : Nat → F) (u : F)
    (flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0)
    (cubic : rho 189649=sourceFirstCubic u) (alternative : rho 189651=5*u*u*sourceFirstCubic u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 189651+rho 189657=if BalanceMapRoots700.choice u then sourceFirstCubic u else 5*u*u*sourceFirstCubic u := by
  have raw := MapArithmeticAdapter704.equation MapArithmeticCapture705B01.entry0 MapArithmeticCapture705B01.checked0 rho arithmetic
  change eval rho MapArithmeticCapture705B01.entry0.output=eval rho MapArithmeticCapture705B01.entry0.left*eval rho MapArithmeticCapture705B01.entry0.right at raw
  have out : eval rho MapArithmeticCapture705B01.entry0.output=rho 189657 := by simp only [MapArithmeticCapture705B01.entry0,eval,Int.cast_one,one_mul,add_zero]
  have left : eval rho MapArithmeticCapture705B01.entry0.left=rho 20935 := by simp only [MapArithmeticCapture705B01.entry0,eval,Int.cast_one,one_mul,add_zero]
  have shape : canonical p MapArithmeticCapture705B01.entry0.right=canonical p (subtract [(189649,1)] [(189651,1)]) := by decide +kernel
  have right : eval rho MapArithmeticCapture705B01.entry0.right=rho 189649-rho 189651 := by
    rw [canonical_equal rho _ _ shape,eval_subtract]
    simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [out,left,right,flag,cubic,alternative] at raw
  rw [alternative]
  cases h : BalanceMapRoots700.choice u <;> simp only [h,Bool.false_eq_true,if_false,if_true,zero_mul,one_mul] at raw ⊢ <;> linear_combination raw

noncomputable def assertionRows : List Row :=
  [⟨[(20936,1)],[(189649,5),(189653,1)]⟩,⟨[(20937,1)],[(189651,1),(189657,1)]⟩]
theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+20997) 2 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (u : F)
    (one : rho copy=1) (input : eval rho MapFirstCubic707.hashInput=u)
    (inverse : rho 20934=(sourceDenominator u)⁻¹)
    (flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0)
    (qr : rho 20936=BalanceMapRoots700.qrRoot u)
    (selected : rho 20937=BalanceMapRoots700.selectedRoot u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20997+i)) 2 := by
  have cubic := MapFirstCubic707.first_cubic rho u one inverse arithmetic
  have q := MapFirstCubic707.q_value rho u input arithmetic
  have alternative := alternative_value rho u q cubic arithmetic
  have qrTarget := qr_target rho u flag cubic arithmetic
  have yTarget := y_target rho u flag cubic alternative arithmetic
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+20997) 2 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  · simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat]
    change rho 20936*rho 20936=5*rho 189649+rho 189653
    rw [qr,qrTarget]
    simpa only [pow_two] using BalanceMapRoots700.qr_square u
  · simp only [eval,Int.cast_one,one_mul,add_zero]
    change rho 20937*rho 20937=rho 189651+rho 189657
    rw [selected,yTarget]
    simpa only [pow_two] using BalanceMapRoots700.selected_square u
end ShielddSecurity.MapRootRows708

set_option pp.all true in
#check @ShielddSecurity.MapRootRows708.qr_target
#print axioms ShielddSecurity.MapRootRows708.qr_target

set_option pp.all true in
#check @ShielddSecurity.MapRootRows708.alternative_value
#print axioms ShielddSecurity.MapRootRows708.alternative_value

set_option pp.all true in
#check @ShielddSecurity.MapRootRows708.y_target
#print axioms ShielddSecurity.MapRootRows708.y_target

set_option pp.all true in
#check @ShielddSecurity.MapRootRows708.captured
#print axioms ShielddSecurity.MapRootRows708.captured

set_option pp.all true in
#check @ShielddSecurity.MapRootRows708.rows
#print axioms ShielddSecurity.MapRootRows708.rows
