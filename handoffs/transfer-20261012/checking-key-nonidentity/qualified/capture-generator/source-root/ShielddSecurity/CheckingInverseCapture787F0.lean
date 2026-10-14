-- GENERATED from data.json and maintained templates. Do not hand edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.CheckingBase598
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingInverseCapture787F0
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def entry : Entry := ⟨943332,false,[(9057,1)],[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(124082,1)],[(124083,1)],101344,[⟨[(9057,1),(121570,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2613035198500699080012737903016384954916552590968062488514021062113153911183)],[(124083,1)]⟩,⟨[(9057,1),(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(124082,4),(124083,1)]⟩]⟩
noncomputable def assertionRows : List Row := [⟨[(124082,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[]⟩]

theorem checked : check entry=true := by decide +kernel

theorem equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 124082=rho 9057*eval rho CheckingBase598.baseX := by
  have result := MapArithmeticAdapter704.equation entry checked rho arithmetic
  simpa only [entry,CheckingBase598.baseX,eval,Int.cast_one,one_mul,add_zero,Bool.false_eq_true,if_false] using result

theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8829) 1 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 124082=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8829+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+8829) 1 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(124082,(p:Int)-1),(copy,1)]*eval rho [(124082,(p:Int)-1),(copy,1)]=eval rho []
  have shape : canonical p [(124082,(p:Int)-1),(copy,1)]=canonical p [(124082,-1),(copy,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]
end ShielddSecurity.CheckingInverseCapture787F0

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseCapture787F0.checked
#print axioms ShielddSecurity.CheckingInverseCapture787F0.checked

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseCapture787F0.equation
#print axioms ShielddSecurity.CheckingInverseCapture787F0.equation

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseCapture787F0.captured
#print axioms ShielddSecurity.CheckingInverseCapture787F0.captured

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseCapture787F0.rows
#print axioms ShielddSecurity.CheckingInverseCapture787F0.rows
