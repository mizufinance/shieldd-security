import ShielddSecurity.CapturedAssetCanonical112
import ShielddSecurity.SelectedComparisonSound159
import ShielddSecurity.BooleanDecode150
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAssetDecode160
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 BinaryComparison100
variable {F : Type} [Field F]
noncomputable def value (rho : Nat → F) : Nat := binary (BooleanDecode150.decoded (CapturedRegistryAssetRange109.columns.map rho))
theorem booleans (rho : Nat → F) (truth : TruthAt rho CapturedRegistryAssetRange109.block.recipe 256) :
    ∀ x∈CapturedRegistryAssetRange109.columns.map rho,Square x x := by
  have parts:=(CapturedRegistryAssetRange109.truth_iff rho).mp truth
  intro x member
  obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
  change column∈List.range' 471 255 at present
  obtain ⟨offset,bound,same⟩:=List.mem_range'.mp present
  simp only [one_mul] at same
  rw [same]
  exact parts.1 offset bound
theorem finite (rho : Nat → F) : value rho<2^255 := by
  simpa only [value,CapturedRegistryAssetRange109.columns,List.length_map,List.length_range'] using
    BooleanDecode150.decoded_bound (CapturedRegistryAssetRange109.columns.map rho)
theorem meaning (rho : Nat → F) (truth : TruthAt rho CapturedRegistryAssetRange109.block.recipe 256) :
    (value rho:F)=rho 6 :=
  (BooleanDecode150.decoded_value _ (booleans rho truth)).trans ((CapturedRegistryAssetRange109.truth_iff rho).mp truth).2
theorem bits (rho : Nat → F) (truth : TruthAt rho CapturedRegistryAssetRange109.block.recipe 256) :
    ∀ index<255,rho (471+index)=bit (F:=F) (CapturedValueComparison106.bitAt (value rho) (216+index)) := by
  have encoding : encodeBits 255 (value rho)=BooleanDecode150.decoded (CapturedRegistryAssetRange109.columns.map rho) := by
    simpa only [value,BooleanDecode150.decoded,List.length_map,CapturedRegistryAssetRange109.columns,List.length_range'] using
      BooleanDecode150.encode_binary (BooleanDecode150.decoded (CapturedRegistryAssetRange109.columns.map rho))
  have fields : (encodeBits 255 (value rho)).map (bit (F:=F))=CapturedRegistryAssetRange109.columns.map rho := by
    rw [encoding]
    exact BooleanDecode150.decoded_fields _ (booleans rho truth)
  intro index bound
  have left : index<((encodeBits 255 (value rho)).map (bit (F:=F))).length := by simpa only [List.length_map,encodeBits_length] using bound
  have right : index<(CapturedRegistryAssetRange109.columns.map rho).length := by
    simpa only [List.length_map,CapturedRegistryAssetRange109.columns,List.length_range'] using bound
  have point:=congrArg (fun xs : List F => xs[index]?.getD 0) fields
  change ((encodeBits 255 (value rho)).map (bit (F:=F)))[index]?.getD 0=(CapturedRegistryAssetRange109.columns.map rho)[index]?.getD 0 at point
  rw [List.getElem?_eq_getElem left,List.getElem?_eq_getElem right] at point
  simp only [Option.getD_some,List.getElem_map,CapturedRegistryAssetRange109.columns,List.getElem_range',Nat.one_mul] at point
  have bitBound : index<(encodeBits 255 (value rho)).length := by simpa only [encodeBits_length] using bound
  simp only [CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem bitBound]
  exact point.symm
variable [CharP F p]
theorem range_truth (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    TruthAt rho CapturedRegistryAssetRange109.block.recipe 256 := by
  have localRows : SatisfiesAt rho CapturedRegistryAssetRange109.block.actual 256 := by
    intro index bound row found
    apply satisfied (178377+index) (by omega) row
    rw [CapturedRegistryAssetRange109.full_position index bound]
    exact found
  exact (CompilerAssertionBlock51.satisfies_iff copy 256 CapturedRegistryAssetRange109.block rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2)).mp localRows
theorem scan_exact (rho : Nat → F) (n : Nat) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<255,rho (471+index)=bit (F:=F) (CapturedValueComparison106.bitAt n (216+index))) :
    1-rho 725+rho 33260=compare (F:=F) (CapturedValueComparison106.pairs n) := by
  have seed : ∀ index<255,(fun column => rho (AssetComparison110.rename column)) (216+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index)) := by
    intro index before
    have renamed : AssetComparison110.rename (216+index)=471+index := by
      unfold AssetComparison110.rename
      rw [if_pos (show 216≤216+index ∧ 216+index<471 by omega)]
      omega
    change rho (AssetComparison110.rename (216+index))=_
    rw [renamed]
    exact values index before
  have linked : (fun column => rho (AssetComparison110.rename column)) copy=1 := by
    simpa only [AssetComparison110.copy_fixed] using one
  have result:=SelectedComparisonSound159.selected_scan (fun column => rho (AssetComparison110.rename column)) n linked
    (AssetComparison111.pullback_satisfies rho arithmetic) seed
  have last : AssetComparison110.rename 470=725 := by decide
  have pivot : AssetComparison110.rename 32752=33260 := by decide
  simpa only [last,pivot] using result
theorem canonical_truth (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
    1-rho 725+rho 33260=1 := by
  have linked:=(CapturedFullRelation58.verifier_links rho satisfied).2.2
  have localRows : SatisfiesAt rho CapturedAssetCanonical112.block.actual 2 := by
    intro index bound row found
    apply satisfied (178633+index) (by omega) row
    rw [CapturedAssetCanonical112.full_position index bound]
    exact found
  have truth:=(CompilerAssertionBlock51.satisfies_iff copy 2 CapturedAssetCanonical112.block rho linked).mp localRows
  have value:=truth 1 (by decide) (true,CapturedAssetCanonical112.expected 1)
    (CapturedAssetCanonical112.hint_exact 1 (by decide))
  change eval rho [(0,1)]=eval rho CapturedAssetCanonical112.valueLC at value
  have normalization : canonical p CapturedAssetCanonical112.valueLC=canonical p [(0,1),(725,-1),(33260,1)] := by decide +kernel
  have normalized:=canonical_equal rho CapturedAssetCanonical112.valueLC [(0,1),(725,-1),(33260,1)] normalization
  rw [normalized] at value
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,sub_eq_add_neg,add_assoc] using value.symm
theorem canonical_bound (rho : Nat → F) (n : Nat) (bound : n<2^255)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1)
    (values : ∀ index<255,rho (471+index)=bit (F:=F) (CapturedValueComparison106.bitAt n (216+index))) : n<p := by
  have copyOne:=((CapturedFullRelation58.verifier_links rho satisfied).2.2).trans one
  have scan:=scan_exact rho n copyOne ((CapturedFullRelation58.satisfies_split rho).mp satisfied).1 values
  rw [canonical_truth rho satisfied one,compare_exact,CapturedValueComparison106.left_exact,CapturedValueComparison106.right_exact,
    encodeBits_value 255 n bound,encodeBits_value 255 (p-1) (by decide)] at scan
  have before : n≤p-1 := by
    by_contra notBefore
    rw [if_neg notBefore] at scan
    exact one_ne_zero scan
  have positive : 0<p := by decide
  omega
theorem canonical (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
    value rho<p ∧ (value rho:F)=rho 6 := by
  have truth:=range_truth rho satisfied
  exact ⟨canonical_bound rho (value rho) (finite rho) satisfied one (bits rho truth),meaning rho truth⟩
end ShielddSecurity.CapturedAssetDecode160

set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.value
#print axioms ShielddSecurity.CapturedAssetDecode160.value
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.booleans
#print axioms ShielddSecurity.CapturedAssetDecode160.booleans
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.finite
#print axioms ShielddSecurity.CapturedAssetDecode160.finite
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.meaning
#print axioms ShielddSecurity.CapturedAssetDecode160.meaning
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.bits
#print axioms ShielddSecurity.CapturedAssetDecode160.bits
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.range_truth
#print axioms ShielddSecurity.CapturedAssetDecode160.range_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.scan_exact
#print axioms ShielddSecurity.CapturedAssetDecode160.scan_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.canonical_truth
#print axioms ShielddSecurity.CapturedAssetDecode160.canonical_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.canonical_bound
#print axioms ShielddSecurity.CapturedAssetDecode160.canonical_bound
set_option pp.all true in
#check @ShielddSecurity.CapturedAssetDecode160.canonical
#print axioms ShielddSecurity.CapturedAssetDecode160.canonical
