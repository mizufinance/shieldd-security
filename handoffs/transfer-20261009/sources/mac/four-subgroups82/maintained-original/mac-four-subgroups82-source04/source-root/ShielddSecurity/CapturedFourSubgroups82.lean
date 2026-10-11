import ShielddSecurity.CapturedFourSubgroups82Check01
import ShielddSecurity.CapturedFourSubgroups82Check02
import ShielddSecurity.CapturedFourSubgroups82Check03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFourSubgroups82
theorem checked (group : Fin 3) : rowCheck group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact CapturedFourSubgroups82Check01.checked
  · exact CapturedFourSubgroups82Check02.checked
  · exact CapturedFourSubgroups82Check03.checked
variable {F : Type} [Field F] [CharP F TransferFirstSubgroupData01.p]
theorem all_four (rho : Nat → F) (one : rho 0=1)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    (Group.OnCurve (CapturedFirstSubgroup81.d:F) (⟨rho 16,rho 17⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) ⟨rho 16,rho 17⟩=⟨rho 14,rho 15⟩) ∧
    (Group.OnCurve (CapturedFirstSubgroup81.d:F) (⟨rho 25,rho 26⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) ⟨rho 25,rho 26⟩=⟨rho 23,rho 24⟩) ∧
    (Group.OnCurve (CapturedFirstSubgroup81.d:F) (⟨rho 37,rho 38⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) ⟨rho 37,rho 38⟩=⟨rho 35,rho 36⟩) ∧
    (Group.OnCurve (CapturedFirstSubgroup81.d:F) (⟨rho 44,rho 45⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) ⟨rho 44,rho 45⟩=⟨rho 42,rho 43⟩) := by
  exact ⟨CapturedFirstSubgroup81.full_source rho one sat,
    source rho one ⟨0,by decide⟩ (checked _) sat,source rho one ⟨1,by decide⟩ (checked _) sat,source rho one ⟨2,by decide⟩ (checked _) sat⟩
end ShielddSecurity.CapturedFourSubgroups82

set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.checked
#print axioms ShielddSecurity.CapturedFourSubgroups82.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.all_four
#print axioms ShielddSecurity.CapturedFourSubgroups82.all_four
