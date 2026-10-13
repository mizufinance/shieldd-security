import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
import ShielddSecurity.AuthorizationFixedSelectors481B000
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedInitialCapture498
open PointEqualityAdapter440
def entries : List Entry := [⟨[(4019,1)],[(4020,1)],[(3767,4139425550610461525665941076812662132363359224232624900223172373014329534291),(62436,1)],[(3767,39635691377166599497441725607757882405510648532010642268690928210480481875247),(62438,1),(200692,1)],4028,[⟨[(3767,48296449624515728953781799431373303705327193276295012922380486326924251650222),(4019,1),(62436,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩,⟨[(3767,12800183797959590982006014900428083432179903968516995553912730489458099309266),(4020,1),(62438,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]⟩]
theorem checked : entries.all check=true := by decide +kernel
end ShielddSecurity.AuthorizationFixedInitialCapture498

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitialCapture498.entries
#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.entries

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitialCapture498.checked
#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.checked

namespace ShielddSecurity.AuthorizationFixedInitialCapture498
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
def selector : FixedSelectorAdapter480.Entry := AuthorizationFixedSelectors481B000.entries[0]
theorem selector_checked : FixedSelectorAdapter480.check selector=true :=
  List.all_eq_true.mp AuthorizationFixedSelectors481B000.checked _ (List.getElem_mem (by decide))
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+4028+i)) 2 ↔
      columnPoint rho 4019=Group.windowPoint (rho 3767) (rho 3768)
        (FixedSelectorAdapter480.base selector) (FixedSelectorAdapter480.twice selector)
        (FixedSelectorAdapter480.triple selector) := by
  have checked := List.all_eq_true.mp checked entries[0] (List.getElem_mem (by decide))
  have equivalence := PointEqualityAdapter440.equality_iff entries[0] checked rho
  have x : canonical p entries[0].expectedX=canonical p selector.outputX := by decide +kernel
  have y : canonical p entries[0].expectedY=canonical p selector.outputY := by decide +kernel
  rw [canonical_equal rho _ _ x,canonical_equal rho _ _ y] at equivalence
  have outputX : entries[0].outputX=[(4019,1)] := rfl
  have outputY : entries[0].outputY=[(4020,1)] := rfl
  rw [outputX,outputY] at equivalence
  simp only [eval,Int.cast_one,one_mul,add_zero] at equivalence
  rw [FixedSelectorAdapter480.coordinates selector selector_checked rho one arithmetic] at equivalence
  exact equivalence
end ShielddSecurity.AuthorizationFixedInitialCapture498

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitialCapture498.selector
#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.selector

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitialCapture498.selector_checked
#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.selector_checked

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitialCapture498.rows_iff
#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.rows_iff
