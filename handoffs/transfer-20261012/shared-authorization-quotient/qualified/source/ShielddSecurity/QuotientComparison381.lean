import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.QuotientComparison381
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨1997,false,[(1996,-1),(200692,1)],[(50200,1)],50200,50201,[⟨[(1996,((p:Int)-1)),(1997,1)],[(50201,1)]⟩,⟨[(1996,((p:Int)-1)),(1997,((p:Int)-1)),(200692,2)],[(50200,4),(50201,1)]⟩]⟩,⟨1998,false,[(50200,1)],[(50202,1)],50202,50203,[⟨[(1998,1),(50200,1),(200692,((p:Int)-1))],[(50203,1)]⟩,⟨[(1998,((p:Int)-1)),(50200,1),(200692,1)],[(50202,4),(50203,1)]⟩]⟩,⟨1999,true,[(50202,1)],[(1999,-1),(50204,1),(200692,1)],50204,50205,[⟨[(1999,((p:Int)-1)),(50202,1)],[(50205,1)]⟩,⟨[(1999,1),(50202,1)],[(50204,4),(50205,1)]⟩]⟩]
def initial : Linear := [(1996,-1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 27462 6 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(1999,-1),(50204,1),(200692,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 27462 6 actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.QuotientComparison381

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.entries
#print axioms ShielddSecurity.QuotientComparison381.entries

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.initial
#print axioms ShielddSecurity.QuotientComparison381.initial

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.actualRows
#print axioms ShielddSecurity.QuotientComparison381.actualRows

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.productionCheck
#print axioms ShielddSecurity.QuotientComparison381.productionCheck

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.production_checked
#print axioms ShielddSecurity.QuotientComparison381.production_checked

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.rowCheck
#print axioms ShielddSecurity.QuotientComparison381.rowCheck

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.rows_checked
#print axioms ShielddSecurity.QuotientComparison381.rows_checked

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.output_exact
#print axioms ShielddSecurity.QuotientComparison381.output_exact

set_option pp.all true in
#check @ShielddSecurity.QuotientComparison381.semantic
#print axioms ShielddSecurity.QuotientComparison381.semantic
