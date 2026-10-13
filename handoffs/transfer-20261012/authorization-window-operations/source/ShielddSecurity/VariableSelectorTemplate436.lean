import ShielddSecurity.CompilerArithmeticTransport41
import ShielddSecurity.GroupWindows
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableSelectorTemplate436
open Compiler CompilerArithmeticTransport41

/-- Ports: one, low/high, base/twice/triple coordinates, then six product/auxiliary pairs. -/
def productRows (left right output auxiliary : Linear) : List Row :=
  [⟨subtract left right,auxiliary⟩,⟨left ++ right,scaleLinear 4 output ++ auxiliary⟩]
def arithmeticRows : List Row :=
  productRows [(1,1)] [(7,1),(5,-1)] [(9,1)] [(10,1)] ++
  productRows [(1,1)] [(3,1)] [(11,1)] [(12,1)] ++
  productRows [(2,1)] [(5,1),(9,1),(11,-1)] [(13,1)] [(14,1)] ++
  productRows [(1,1)] [(8,1),(6,-1)] [(15,1)] [(16,1)] ++
  productRows [(1,1)] [(4,1),(0,-1)] [(17,1)] [(18,1)] ++
  productRows [(2,1)] [(6,1),(15,1),(0,-1),(17,-1)] [(19,1)] [(20,1)]

variable {F : Type} [Field F] [CharP F p]
theorem values (rho : Nat → F) (one : rho 0=1) (arithmetic : Satisfies rho arithmeticRows) :
    rho 9=rho 1*(rho 7-rho 5) ∧ rho 11=rho 1*rho 3 ∧
    rho 13=rho 2*(rho 5+rho 9-rho 11) ∧
    rho 15=rho 1*(rho 8-rho 6) ∧ rho 17=rho 1*(rho 4-1) ∧
    rho 19=rho 2*(rho 6+rho 15-1-rho 17) := by
  have a := checked_product_sound rho arithmeticRows [(1,1)] [(7,1),(5,-1)] [(9,1)] [(10,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have b := checked_product_sound rho arithmeticRows [(1,1)] [(3,1)] [(11,1)] [(12,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have c := checked_product_sound rho arithmeticRows [(2,1)] [(5,1),(9,1),(11,-1)] [(13,1)] [(14,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have e := checked_product_sound rho arithmeticRows [(1,1)] [(8,1),(6,-1)] [(15,1)] [(16,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have f := checked_product_sound rho arithmeticRows [(1,1)] [(4,1),(0,-1)] [(17,1)] [(18,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  have g := checked_product_sound rho arithmeticRows [(2,1)] [(6,1),(15,1),(0,-1),(17,-1)] [(19,1)] [(20,1)]
    four_ne_zero arithmetic (by decide +kernel) (by decide +kernel)
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,mul_one] at a b c e f g
  exact ⟨by simpa only [sub_eq_add_neg] using a,b,
    by simpa only [sub_eq_add_neg,add_assoc] using c,
    by simpa only [sub_eq_add_neg] using e,
    by simpa only [sub_eq_add_neg] using f,
    by simpa only [sub_eq_add_neg,add_assoc] using g⟩

def output {F : Type} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨rho 11+rho 13,rho 0+rho 17+rho 19⟩

theorem coordinates (rho : Nat → F) (one : rho 0=1)
    (arithmetic : Satisfies rho arithmeticRows) :
    output rho = Group.windowPoint (rho 1) (rho 2)
      ⟨rho 3,rho 4⟩ ⟨rho 5,rho 6⟩ ⟨rho 7,rho 8⟩ := by
  obtain ⟨a,b,c,e,f,g⟩ := values rho one arithmetic
  simp only [output,Group.windowPoint,Group.chooseCoordinate,one,c,g,a,b,e,f]
  congr 1 <;> ring
end ShielddSecurity.VariableSelectorTemplate436

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorTemplate436.productRows
#print axioms ShielddSecurity.VariableSelectorTemplate436.productRows

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorTemplate436.arithmeticRows
#print axioms ShielddSecurity.VariableSelectorTemplate436.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorTemplate436.values
#print axioms ShielddSecurity.VariableSelectorTemplate436.values

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorTemplate436.output
#print axioms ShielddSecurity.VariableSelectorTemplate436.output

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorTemplate436.coordinates
#print axioms ShielddSecurity.VariableSelectorTemplate436.coordinates
