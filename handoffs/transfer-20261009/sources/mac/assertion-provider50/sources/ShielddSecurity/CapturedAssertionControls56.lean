import ShielddSecurity.CapturedAssertions50B0000
import ShielddSecurity.CapturedAssertions50B0089
import ShielddSecurity.CompilerVerifierLinks53
import ShielddSecurity.CompilerAssertionPairs55
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAssertionControls56
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def first : Row := ⟨[(10,1)],[(10,1)]⟩
noncomputable def hint : Bool × Recipe := (true,.square [(10,1)] [(10,1)])
theorem first_actual : CapturedAssertions50B0000.actual[0]?=some first := by rfl
theorem first_hint : CapturedAssertions50B0000.recipes[0]?=some hint := by rfl
theorem copy_actual : CapturedAssertions50B0089.actual[31]?=some (CompilerVerifierLinks53.linkRow 0 copy) := by rfl
theorem positive : CompilerAssertionPairs55.checkPairs p copy [first] [hint]=true := by decide +kernel
theorem coefficient_rejected : CompilerAssertionPairs55.checkPairs p copy [⟨[(10,2)],[(10,1)]⟩] [hint]=false := by decide +kernel
theorem existing_index_rejected :
    (match CapturedAssertions50B0000.actual[1]? with
      | some row => CompilerAssertionPairs55.checkPairs p copy [row] [hint]
      | none => true)=false := by decide +kernel
theorem omission_rejected : CompilerAssertionPairs55.checkPairs p copy [] [hint]=false := by decide +kernel
theorem copy_positive : CompilerAssertionPairs55.checkPairs p copy [CompilerVerifierLinks53.linkRow 0 copy]
    [(false,.linear [(0,1)] [(copy,1)])]=true := by decide +kernel
theorem copy_rejected : CompilerAssertionPairs55.checkPairs p copy [CompilerVerifierLinks53.linkRow 0 (copy-1)]
    [(false,.linear [(0,1)] [(copy,1)])]=false := by decide +kernel
end ShielddSecurity.CapturedAssertionControls56

set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.first
#print axioms ShielddSecurity.CapturedAssertionControls56.first
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.hint
#print axioms ShielddSecurity.CapturedAssertionControls56.hint
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.first_actual
#print axioms ShielddSecurity.CapturedAssertionControls56.first_actual
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.first_hint
#print axioms ShielddSecurity.CapturedAssertionControls56.first_hint
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.copy_actual
#print axioms ShielddSecurity.CapturedAssertionControls56.copy_actual
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.positive
#print axioms ShielddSecurity.CapturedAssertionControls56.positive
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.coefficient_rejected
#print axioms ShielddSecurity.CapturedAssertionControls56.coefficient_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.existing_index_rejected
#print axioms ShielddSecurity.CapturedAssertionControls56.existing_index_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.omission_rejected
#print axioms ShielddSecurity.CapturedAssertionControls56.omission_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.copy_positive
#print axioms ShielddSecurity.CapturedAssertionControls56.copy_positive
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionControls56.copy_rejected
#print axioms ShielddSecurity.CapturedAssertionControls56.copy_rejected
