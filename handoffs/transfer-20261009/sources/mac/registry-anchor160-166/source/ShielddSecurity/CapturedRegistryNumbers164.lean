import ShielddSecurity.CapturedRegulatedSound163
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryNumbers164
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem registry_numbers (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) :
    ∃ value asset next : Nat,value<p ∧ asset<p ∧ next<p ∧
      (value:F)=rho 11 ∧ (asset:F)=rho 6 ∧ (next:F)=rho 13 ∧
      ((rho 10=0 ∧ value<asset ∧ asset<next) ∨ (rho 10=1 ∧ asset=value)) := by
  have originals:=CapturedRegistryOrderSound162.canonical_originals rho satisfied one
  refine ⟨CapturedValueDecode158.value rho,CapturedAssetDecode160.value rho,CapturedNextDecode161.value rho,
    originals.1.1,originals.2.1.1,originals.2.2.1,originals.1.2,originals.2.1.2,originals.2.2.2,?_⟩
  rcases CapturedRegulatedSound163.role_cases rho satisfied with off|on
  · exact Or.inl ⟨off,CapturedRegistryOrderSound162.unregulated rho satisfied one off⟩
  · exact Or.inr ⟨on,CapturedRegulatedSound163.regulated_equal rho satisfied one on⟩
end ShielddSecurity.CapturedRegistryNumbers164

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNumbers164.registry_numbers
#print axioms ShielddSecurity.CapturedRegistryNumbers164.registry_numbers
