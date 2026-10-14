-- GENERATED from data.json and maintained templates. Do not hand edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RecoveryInverseCapture779F1
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def entry : Entry := ⟨746765,false,[(7596,1)],[(6326,1)],[(106556,1)],[(106557,1)],83818,[⟨[(6326,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7596,1)],[(106557,1)]⟩,⟨[(6326,1),(7596,1)],[(106556,4),(106557,1)]⟩]⟩
noncomputable def assertionRows : List Row := [⟨[(106556,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[]⟩]

theorem checked : check entry=true := by decide +kernel

theorem equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 106556=rho 7596*rho 6326 := by
  have result := MapArithmeticAdapter704.equation entry checked rho arithmetic
  simpa only [entry,eval,Int.cast_one,one_mul,add_zero,Bool.false_eq_true,if_false] using result

theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7455) 1 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 106556=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7455+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7455) 1 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(106556,(p:Int)-1),(copy,1)]*eval rho [(106556,(p:Int)-1),(copy,1)]=eval rho []
  have shape : canonical p [(106556,(p:Int)-1),(copy,1)]=canonical p [(106556,-1),(copy,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]
end ShielddSecurity.RecoveryInverseCapture779F1

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseCapture779F1.checked
#print axioms ShielddSecurity.RecoveryInverseCapture779F1.checked

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseCapture779F1.equation
#print axioms ShielddSecurity.RecoveryInverseCapture779F1.equation

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseCapture779F1.captured
#print axioms ShielddSecurity.RecoveryInverseCapture779F1.captured

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseCapture779F1.rows
#print axioms ShielddSecurity.RecoveryInverseCapture779F1.rows
