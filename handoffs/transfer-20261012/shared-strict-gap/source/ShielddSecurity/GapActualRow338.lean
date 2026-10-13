import ShielddSecurity.CapturedRegistryGap146
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.GapActualRow338
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem of_value (rho : Nat → F) (value : rho 33788=0) :
    CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 := by
  have normal : Satisfies rho CapturedRegistryGap146.normalizedRows := by
    intro row member
    have same : row=⟨[(33788,-1)],[]⟩ := by simpa only [CapturedRegistryGap146.normalizedRows,List.mem_singleton] using member
    subst row
    change Square (eval rho [(33788,-1)]) (eval rho [])
    simp only [eval,value,Int.cast_neg,Int.cast_one,mul_zero,add_zero,Square]
  have actual := transfer rho CapturedRegistryGap146.actualRows CapturedRegistryGap146.normalizedRows
    CapturedRegistryGap146.reverse_checked normal
  intro index bound row found
  exact actual row (List.mem_iff_getElem?.mpr ⟨index,(CapturedRegistryGap146.actual_position index bound).symm.trans found⟩)
end ShielddSecurity.GapActualRow338
set_option pp.all true in
#check @ShielddSecurity.GapActualRow338.of_value
#print axioms ShielddSecurity.GapActualRow338.of_value
