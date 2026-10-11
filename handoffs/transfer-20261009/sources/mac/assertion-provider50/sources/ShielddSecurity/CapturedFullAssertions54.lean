import ShielddSecurity.CapturedAssertions54G00
import ShielddSecurity.CapturedAssertions54G01
import ShielddSecurity.CapturedAssertions54G02
import ShielddSecurity.CapturedAssertions54G03
import ShielddSecurity.CapturedAssertions54G04
import ShielddSecurity.CapturedAssertions54G05
import ShielddSecurity.CompilerAssertionBlock51
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFullAssertions54
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def block : Block p copy 22816 := (CompilerAssertionBlock51.append p copy 12288 10528 (CompilerAssertionBlock51.append p copy 4096 8192 CapturedAssertions54G00.block (CompilerAssertionBlock51.append p copy 4096 4096 CapturedAssertions54G01.block CapturedAssertions54G02.block)) (CompilerAssertionBlock51.append p copy 4096 6432 CapturedAssertions54G03.block (CompilerAssertionBlock51.append p copy 4096 2336 CapturedAssertions54G04.block CapturedAssertions54G05.block)))
noncomputable def rowAt := block.actual
noncomputable def recipeAt := block.recipe
theorem every_position (index : Nat) (bound : index<22816) : ∃ row,rowAt index=some row :=
  CompilerAssertionBlock51.every_position p copy 22816 block index bound
variable {F : Type} [Field F] [CharP F p]
theorem satisfies_iff (rho : Nat → F) (linked : rho copy=rho 0) :
    CompilerAssertionBlock51.SatisfiesAt rho rowAt 22816 ↔
    CompilerAssertionBlock51.TruthAt rho recipeAt 22816 :=
  CompilerAssertionBlock51.satisfies_iff copy 22816 block rho linked
end ShielddSecurity.CapturedFullAssertions54

set_option pp.all true in
#check @ShielddSecurity.CapturedFullAssertions54.block
#print axioms ShielddSecurity.CapturedFullAssertions54.block
set_option pp.all true in
#check @ShielddSecurity.CapturedFullAssertions54.rowAt
#print axioms ShielddSecurity.CapturedFullAssertions54.rowAt
set_option pp.all true in
#check @ShielddSecurity.CapturedFullAssertions54.recipeAt
#print axioms ShielddSecurity.CapturedFullAssertions54.recipeAt
set_option pp.all true in
#check @ShielddSecurity.CapturedFullAssertions54.every_position
#print axioms ShielddSecurity.CapturedFullAssertions54.every_position
set_option pp.all true in
#check @ShielddSecurity.CapturedFullAssertions54.satisfies_iff
#print axioms ShielddSecurity.CapturedFullAssertions54.satisfies_iff
