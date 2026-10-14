-- GENERATED from maintained exact data/template; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesCapture800F1
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
noncomputable def rows : List Row := [⟨[(6195,52435875175126190479447740508185965837690552500527637822603658699938581184512),(6325,1)],[]⟩]
theorem checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7460) 1 rows=true := by decide +kernel

theorem satisfies (rho : Nat → F) (equal : rho 6195=rho 6325) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7460+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7460) 1 rows checked rho).mp
  intro row member
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(6195,(p:Int)-1),(6325,1)]*
    eval rho [(6195,(p:Int)-1),(6325,1)]=eval rho []
  have shape : canonical p [(6195,(p:Int)-1),(6325,1)]=
    canonical p [(6195,-1),(6325,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,equal]
  ring
end ShielddSecurity.SemanticCopiesCapture800F1

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesCapture800F1.checked
#print axioms ShielddSecurity.SemanticCopiesCapture800F1.checked

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesCapture800F1.satisfies
#print axioms ShielddSecurity.SemanticCopiesCapture800F1.satisfies
