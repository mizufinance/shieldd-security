import ShielddSecurity.ClampNumeric400
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedAssertions50B0008
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedClampRows401
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def arithmeticRows : List Row :=
  [⟨[(1999,1),(51208,(p:Int)-1),(copy,1)],[(51210,4),(51211,1)]⟩,
   ⟨[(1999,1),(51208,1),(copy,(p:Int)-1)],[(51211,1)]⟩]

def orderedRows : List Row := arithmeticRows.reverse

noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 28472 2 orderedRows

theorem rows_checked : rowCheck=true := by decide +kernel

theorem minus_checked : checkRow p arithmeticRows
    ⟨subtract [(1999,1)] [(copy,1),(51208,-1)],[(51211,1)]⟩ = true := by decide +kernel

theorem plus_checked : checkRow p arithmeticRows
    ⟨[(1999,1)]++[(copy,1),(51208,-1)],[(51211,1)]++scaleLinear 4 [(51210,1)]⟩ = true := by decide +kernel

def expected (index : Nat) : Recipe :=
  if index=0 then .square [(51208,1)] [(51208,1)] else .linear [] [(51210,1)]

noncomputable def block : Block p copy 2 where
  actual := fun index => CapturedAssertions50B0008.block.actual (206+index)
  recipe := fun index => CapturedAssertions50B0008.block.recipe (206+index)
  exact_checked := by
    intro index bound
    exact CapturedAssertions50B0008.block.exact_checked (206+index) (by omega)

theorem hint_exact (index : Nat) (bound : index<2) : block.recipe index=some (true,expected index) := by
  have cases : index=0 ∨ index=1 := by omega
  rcases cases with rfl|rfl <;> rfl

theorem full_position_checked : (List.range 2).all (fun index => decide
    (CapturedFullRelation58.rowAt (180208+index)=block.actual index)) = true := by decide +kernel

theorem full_position (index : Nat) (bound : index<2) :
    CapturedFullRelation58.rowAt (180208+index)=block.actual index :=
  of_decide_eq_true (List.all_eq_true.mp full_position_checked index (List.mem_range.mpr bound))

variable {F : Type} [Field F] [CharP F p]

theorem product (rho : Nat → F) (zero : rho 0=1) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 51210=rho 1999*(1-rho 51208) := by
  have selected := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 28472 2 orderedRows rows_checked (by decide) rho arithmetic
  have checked := checked_product_sound rho arithmeticRows [(1999,1)] [(copy,1),(51208,-1)] [(51210,1)] [(51211,1)] four_ne_zero
  have satisfied : Satisfies rho arithmeticRows := by
    intro row member
    exact selected row (List.mem_reverse.mpr member)
  have result := checked satisfied minus_checked plus_checked
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,sub_eq_add_neg] using result

theorem complete (rho : Nat → F) (zero : rho 0=1) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (boolean : Square (rho 51208) (rho 51208)) (gate : rho 1999*(1-rho 51208)=0) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (180208+index)) 2 := by
  have value := (product rho zero one arithmetic).trans gate
  have truth : TruthAt rho block.recipe 2 := by
    intro index before hint found
    have same : hint=(true,expected index) := Option.some.inj (found.symm.trans (hint_exact index before))
    subst hint
    have cases : index=0 ∨ index=1 := by omega
    rcases cases with rfl|rfl
    · change Square (eval rho [(51208,1)]) (eval rho [(51208,1)])
      simpa only [eval,Int.cast_one,one_mul,add_zero] using boolean
    · change eval rho []=eval rho [(51210,1)]
      simp only [eval,Int.cast_one,one_mul,add_zero,value]
  have localRows := (satisfies_iff copy 2 block rho (one.trans zero.symm)).mpr truth
  intro index before row found
  change CapturedFullRelation58.rowAt (180208+index)=some row at found
  rw [full_position index before] at found
  exact localRows index before row found

end ShielddSecurity.CapturedClampRows401

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.arithmeticRows
#print axioms ShielddSecurity.CapturedClampRows401.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.orderedRows
#print axioms ShielddSecurity.CapturedClampRows401.orderedRows

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.rowCheck
#print axioms ShielddSecurity.CapturedClampRows401.rowCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.rows_checked
#print axioms ShielddSecurity.CapturedClampRows401.rows_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.minus_checked
#print axioms ShielddSecurity.CapturedClampRows401.minus_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.plus_checked
#print axioms ShielddSecurity.CapturedClampRows401.plus_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.expected
#print axioms ShielddSecurity.CapturedClampRows401.expected

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.block
#print axioms ShielddSecurity.CapturedClampRows401.block

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.hint_exact
#print axioms ShielddSecurity.CapturedClampRows401.hint_exact

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.full_position_checked
#print axioms ShielddSecurity.CapturedClampRows401.full_position_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.full_position
#print axioms ShielddSecurity.CapturedClampRows401.full_position

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.product
#print axioms ShielddSecurity.CapturedClampRows401.product

set_option pp.all true in
#check @ShielddSecurity.CapturedClampRows401.complete
#print axioms ShielddSecurity.CapturedClampRows401.complete
