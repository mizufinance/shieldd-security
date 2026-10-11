import ShielddSecurity.CapturedFullAssertions54
import ShielddSecurity.CompilerVerifierLinks53
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAssertionLinks57
open CompilerAssertionBlock51 CompilerArithmeticTransport41 CompilerVerifierLinks53
theorem public_row : CapturedFullAssertions54.rowAt 22813=some (linkRow 1 22737) := by rfl
theorem committed_row : CapturedFullAssertions54.rowAt 22814=some (linkRow 2 9) := by rfl
theorem copy_row : CapturedFullAssertions54.rowAt 22815=some (linkRow 0 copy) := by rfl
theorem copy_recipe : CapturedFullAssertions54.recipeAt 22815=some (false,Recipe.linear [(0,1)] [(copy,1)]) := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem public_of_satisfies (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullAssertions54.rowAt 22816) : rho 1=rho 22737 :=
  (link_iff rho 1 22737).mp (satisfied 22813 (by decide) _ public_row)
theorem committed_of_satisfies (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullAssertions54.rowAt 22816) : rho 2=rho 9 :=
  (link_iff rho 2 9).mp (satisfied 22814 (by decide) _ committed_row)
theorem copy_of_satisfies (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullAssertions54.rowAt 22816) : rho copy=rho 0 :=
  ((link_iff rho 0 copy).mp (satisfied 22815 (by decide) _ copy_row)).symm
omit [CharP F p] in
theorem copy_of_truth (rho : Nat → F)
    (truth : TruthAt rho CapturedFullAssertions54.recipeAt 22816) : rho copy=rho 0 := by
  have h:=truth 22815 (by decide) _ copy_recipe
  change eval rho [(0,1)]=eval rho [(copy,1)] at h
  simpa only [eval,Int.cast_one,one_mul,add_zero] using h.symm
theorem satisfies_iff (rho : Nat → F) :
    SatisfiesAt rho CapturedFullAssertions54.rowAt 22816 ↔
    TruthAt rho CapturedFullAssertions54.recipeAt 22816 := by
  constructor
  · intro satisfied
    exact (CapturedFullAssertions54.satisfies_iff rho (copy_of_satisfies rho satisfied)).mp satisfied
  · intro truth
    exact (CapturedFullAssertions54.satisfies_iff rho (copy_of_truth rho truth)).mpr truth
end ShielddSecurity.CapturedAssertionLinks57

set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.public_row
#print axioms ShielddSecurity.CapturedAssertionLinks57.public_row
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.committed_row
#print axioms ShielddSecurity.CapturedAssertionLinks57.committed_row
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.copy_row
#print axioms ShielddSecurity.CapturedAssertionLinks57.copy_row
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.copy_recipe
#print axioms ShielddSecurity.CapturedAssertionLinks57.copy_recipe
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.public_of_satisfies
#print axioms ShielddSecurity.CapturedAssertionLinks57.public_of_satisfies
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.committed_of_satisfies
#print axioms ShielddSecurity.CapturedAssertionLinks57.committed_of_satisfies
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.copy_of_satisfies
#print axioms ShielddSecurity.CapturedAssertionLinks57.copy_of_satisfies
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.copy_of_truth
#print axioms ShielddSecurity.CapturedAssertionLinks57.copy_of_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedAssertionLinks57.satisfies_iff
#print axioms ShielddSecurity.CapturedAssertionLinks57.satisfies_iff
