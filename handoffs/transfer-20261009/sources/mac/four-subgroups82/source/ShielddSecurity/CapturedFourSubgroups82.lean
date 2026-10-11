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
theorem roles0 : rename ⟨0,by decide⟩ 16=25 ∧ rename ⟨0,by decide⟩ 17=26 ∧ rename ⟨0,by decide⟩ 14=23 ∧ rename ⟨0,by decide⟩ 15=24 := by decide +kernel
theorem roles1 : rename ⟨1,by decide⟩ 16=37 ∧ rename ⟨1,by decide⟩ 17=38 ∧ rename ⟨1,by decide⟩ 14=35 ∧ rename ⟨1,by decide⟩ 15=36 := by decide +kernel
theorem roles2 : rename ⟨2,by decide⟩ 16=44 ∧ rename ⟨2,by decide⟩ 17=45 ∧ rename ⟨2,by decide⟩ 14=42 ∧ rename ⟨2,by decide⟩ 15=43 := by decide +kernel
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
  refine ⟨CapturedFirstSubgroup81.full_source rho one sat,?_,?_,?_⟩
  · have result:=source (F:=F) rho one ⟨0,by decide⟩ (checked _) sat
    simpa only [preimage,point,roles0.1,roles0.2.1,roles0.2.2.1,roles0.2.2.2] using result
  · have result:=source (F:=F) rho one ⟨1,by decide⟩ (checked _) sat
    simpa only [preimage,point,roles1.1,roles1.2.1,roles1.2.2.1,roles1.2.2.2] using result
  · have result:=source (F:=F) rho one ⟨2,by decide⟩ (checked _) sat
    simpa only [preimage,point,roles2.1,roles2.2.1,roles2.2.2.1,roles2.2.2.2] using result
end ShielddSecurity.CapturedFourSubgroups82

set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.checked
#print axioms ShielddSecurity.CapturedFourSubgroups82.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.roles0
#print axioms ShielddSecurity.CapturedFourSubgroups82.roles0
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.roles1
#print axioms ShielddSecurity.CapturedFourSubgroups82.roles1
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.roles2
#print axioms ShielddSecurity.CapturedFourSubgroups82.roles2
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroups82.all_four
#print axioms ShielddSecurity.CapturedFourSubgroups82.all_four
