import ShielddSecurity.CapturedValueCanonicalSound157
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueDecode158
open CompilerAssertionBlock51 CompilerArithmeticTransport41 BinaryComparison100
variable {F : Type} [Field F]
noncomputable def value (rho : Nat → F) : Nat := binary (BooleanDecode150.decoded (CapturedRegistryValueRange97.columns.map rho))
theorem booleans (rho : Nat → F) (truth : TruthAt rho CapturedRegistryValueRange97.block.recipe 256) :
    ∀ x∈CapturedRegistryValueRange97.columns.map rho,Square x x := by
  have parts:=(CapturedRegistryValueRange97.truth_iff rho).mp truth
  intro x member
  obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
  change column∈List.range' 216 255 at present
  obtain ⟨offset,bound,same⟩:=List.mem_range'.mp present
  simp only [one_mul] at same
  rw [same]
  exact parts.1 offset bound
theorem finite (rho : Nat → F) : value rho<2^255 := by
  simpa only [value,CapturedRegistryValueRange97.columns,List.length_map,List.length_range'] using
    BooleanDecode150.decoded_bound (CapturedRegistryValueRange97.columns.map rho)
theorem meaning (rho : Nat → F) (truth : TruthAt rho CapturedRegistryValueRange97.block.recipe 256) :
    (value rho:F)=rho 11 :=
  (BooleanDecode150.decoded_value _ (booleans rho truth)).trans ((CapturedRegistryValueRange97.truth_iff rho).mp truth).2
theorem bits (rho : Nat → F) (truth : TruthAt rho CapturedRegistryValueRange97.block.recipe 256) :
    ∀ index<255,rho (216+index)=bit (F:=F) (CapturedValueComparison106.bitAt (value rho) (216+index)) := by
  have encoding : encodeBits 255 (value rho)=BooleanDecode150.decoded (CapturedRegistryValueRange97.columns.map rho) := by
    simpa only [value,BooleanDecode150.decoded,List.length_map,CapturedRegistryValueRange97.columns,List.length_range'] using
      BooleanDecode150.encode_binary (BooleanDecode150.decoded (CapturedRegistryValueRange97.columns.map rho))
  have fields : (encodeBits 255 (value rho)).map (bit (F:=F))=CapturedRegistryValueRange97.columns.map rho := by
    rw [encoding]
    exact BooleanDecode150.decoded_fields _ (booleans rho truth)
  intro index bound
  have left : index<((encodeBits 255 (value rho)).map (bit (F:=F))).length := by simpa only [List.length_map,encodeBits_length] using bound
  have right : index<(CapturedRegistryValueRange97.columns.map rho).length := by
    simpa only [List.length_map,CapturedRegistryValueRange97.columns,List.length_range'] using bound
  have point:=congrArg (fun xs : List F => xs[index]?.getD 0) fields
  rw [List.getElem?_eq_getElem left,List.getElem?_eq_getElem right] at point
  simp only [Option.getD_some,List.getElem_map,CapturedRegistryValueRange97.columns,List.getElem_range',Nat.one_mul] at point
  have bitBound : index<(encodeBits 255 (value rho)).length := by simpa only [encodeBits_length] using bound
  simp only [CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem bitBound]
  exact point.symm
variable [CharP F p]
theorem range_truth (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    TruthAt rho CapturedRegistryValueRange97.block.recipe 256 := by
  have localRows : SatisfiesAt rho CapturedRegistryValueRange97.block.actual 256 := by
    intro index bound row found
    apply satisfied (178119+index) (by omega) row
    rw [CapturedRegistryValueRange97.full_position index bound]
    exact found
  exact (CompilerAssertionBlock51.satisfies_iff copy 256 CapturedRegistryValueRange97.block rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2)).mp localRows
theorem canonical (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
    value rho<p ∧ (value rho:F)=rho 11 := by
  have truth:=range_truth rho satisfied
  exact ⟨CapturedValueCanonicalSound157.canonical_bound rho (value rho) (finite rho) satisfied one (bits rho truth),meaning rho truth⟩
end ShielddSecurity.CapturedValueDecode158

set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.value
#print axioms ShielddSecurity.CapturedValueDecode158.value
set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.booleans
#print axioms ShielddSecurity.CapturedValueDecode158.booleans
set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.finite
#print axioms ShielddSecurity.CapturedValueDecode158.finite
set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.meaning
#print axioms ShielddSecurity.CapturedValueDecode158.meaning
set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.bits
#print axioms ShielddSecurity.CapturedValueDecode158.bits
set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.range_truth
#print axioms ShielddSecurity.CapturedValueDecode158.range_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedValueDecode158.canonical
#print axioms ShielddSecurity.CapturedValueDecode158.canonical
