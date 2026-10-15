/- Generated from maintained public statement-hash generator; edit generator or templates. -/
import ShielddSecurity.PublicStatementHashComposition975C187B10
import ShielddSecurity.PublicStatementHashPrefix973C187B10R00
import ShielddSecurity.PublicStatementHashPrefix973C187B10R01
import ShielddSecurity.AuthorizationPoseidonRounds528
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementHashPermutation976C187B10
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := PublicStatementHashCapture972C187B10R00.parameters
noncomputable def before := PublicStatementHashCapture972C187B10R00.before
noncomputable def after := PublicStatementHashComposition975C187B10.after 64
noncomputable def result : Linear := [(199830,5579934908212736977238010113730457006906792843192217773053283881663622591681),(199834,50978946942794420813356136484142315443152313428221265043903658432145007475423),(199838,51737743277955608982399432577620617083998176562860787771480331520415801857016),(199842,280754542936071555323583947036382301904172335755315562603417507239324752636),(199846,44773762128641970103070913747625047847186741019957383563700055475244115610384),(199850,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
theorem result_port : after 1=result := by decide +kernel
theorem prefix_seam : PublicStatementHashCapture972C187B10R01.before=PublicStatementHashCapture972C187B10R00.after := rfl
variable {F : Type} [Field F] [CharP F p]
theorem permutation (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (after i))=Poseidon.permute (Poseidon.castParameters parameters)
      (fun i => eval rho (before i)) := by
  have first := PublicStatementHashPrefix973C187B10R00.arbitrary_round rho one linked arithmetic
  have second := PublicStatementHashPrefix973C187B10R01.arbitrary_round rho one linked arithmetic
  rw [prefix_seam,first] at second
  have result := PublicStatementHashComposition975C187B10.suffix rho one linked arithmetic
  rw [second] at result
  exact result.trans (AuthorizationPoseidonRounds528.permutation_bridge _ _)
theorem output (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.permute (Poseidon.castParameters parameters) (fun i => eval rho (before i)) 1 := by
  have value := congrFun (permutation rho one linked arithmetic) 1
  rw [result_port] at value
  exact value
end ShielddSecurity.PublicStatementHashPermutation976C187B10
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPermutation976C187B10.result_port
#print axioms ShielddSecurity.PublicStatementHashPermutation976C187B10.result_port
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPermutation976C187B10.prefix_seam
#print axioms ShielddSecurity.PublicStatementHashPermutation976C187B10.prefix_seam
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPermutation976C187B10.permutation
#print axioms ShielddSecurity.PublicStatementHashPermutation976C187B10.permutation
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPermutation976C187B10.output
#print axioms ShielddSecurity.PublicStatementHashPermutation976C187B10.output
