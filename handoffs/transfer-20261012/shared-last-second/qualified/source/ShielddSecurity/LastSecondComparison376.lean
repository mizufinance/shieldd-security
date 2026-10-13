import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LastSecondComparison376
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨7730,true,[(7729,-1),(200692,1)],[(7730,-1),(108462,1),(200692,1)],108462,108463,[⟨[(7729,((p:Int)-1)),(7730,((p:Int)-1)),(200692,1)],[(108463,1)]⟩,⟨[(7729,((p:Int)-1)),(7730,1),(200692,1)],[(108462,4),(108463,1)]⟩]⟩,⟨7731,false,[(7730,-1),(108462,1),(200692,1)],[(108464,1)],108464,108465,[⟨[(7730,((p:Int)-1)),(7731,1),(108462,1)],[(108465,1)]⟩,⟨[(7730,((p:Int)-1)),(7731,((p:Int)-1)),(108462,1),(200692,2)],[(108464,4),(108465,1)]⟩]⟩,⟨7732,false,[(108464,1)],[(108466,1)],108466,108467,[⟨[(7732,1),(108464,1),(200692,((p:Int)-1))],[(108467,1)]⟩,⟨[(7732,((p:Int)-1)),(108464,1),(200692,1)],[(108466,4),(108467,1)]⟩]⟩,⟨7733,false,[(108466,1)],[(108468,1)],108468,108469,[⟨[(7733,1),(108466,1),(200692,((p:Int)-1))],[(108469,1)]⟩,⟨[(7733,((p:Int)-1)),(108466,1),(200692,1)],[(108468,4),(108469,1)]⟩]⟩,⟨7734,true,[(108468,1)],[(7734,-1),(108470,1),(200692,1)],108470,108471,[⟨[(7734,((p:Int)-1)),(108468,1)],[(108471,1)]⟩,⟨[(7734,1),(108468,1)],[(108470,4),(108471,1)]⟩]⟩,⟨7735,false,[(7734,-1),(108470,1),(200692,1)],[(108472,1)],108472,108473,[⟨[(7734,((p:Int)-1)),(7735,1),(108470,1)],[(108473,1)]⟩,⟨[(7734,((p:Int)-1)),(7735,((p:Int)-1)),(108470,1),(200692,2)],[(108472,4),(108473,1)]⟩]⟩,⟨7736,true,[(108472,1)],[(7736,-1),(108474,1),(200692,1)],108474,108475,[⟨[(7736,((p:Int)-1)),(108472,1)],[(108475,1)]⟩,⟨[(7736,1),(108472,1)],[(108474,4),(108475,1)]⟩]⟩,⟨7737,false,[(7736,-1),(108474,1),(200692,1)],[(108476,1)],108476,108477,[⟨[(7736,((p:Int)-1)),(7737,1),(108474,1)],[(108477,1)]⟩,⟨[(7736,((p:Int)-1)),(7737,((p:Int)-1)),(108474,1),(200692,2)],[(108476,4),(108477,1)]⟩]⟩,⟨7738,true,[(108476,1)],[(7738,-1),(108478,1),(200692,1)],108478,108479,[⟨[(7738,((p:Int)-1)),(108476,1)],[(108479,1)]⟩,⟨[(7738,1),(108476,1)],[(108478,4),(108479,1)]⟩]⟩]
def initial : Linear := [(7729,-1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85724 18 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(7738,-1),(108478,1),(200692,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85724 18 actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.LastSecondComparison376

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.entries
#print axioms ShielddSecurity.LastSecondComparison376.entries

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.initial
#print axioms ShielddSecurity.LastSecondComparison376.initial

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.actualRows
#print axioms ShielddSecurity.LastSecondComparison376.actualRows

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.productionCheck
#print axioms ShielddSecurity.LastSecondComparison376.productionCheck

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.production_checked
#print axioms ShielddSecurity.LastSecondComparison376.production_checked

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.rowCheck
#print axioms ShielddSecurity.LastSecondComparison376.rowCheck

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.rows_checked
#print axioms ShielddSecurity.LastSecondComparison376.rows_checked

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.output_exact
#print axioms ShielddSecurity.LastSecondComparison376.output_exact

set_option pp.all true in
#check @ShielddSecurity.LastSecondComparison376.semantic
#print axioms ShielddSecurity.LastSecondComparison376.semantic
