import ShielddSecurity.CapturedRegistryAssetRange109Data
import ShielddSecurity.CapturedGlobalSubgroup90
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryAssetRange109
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
theorem truth_iff (rho : Nat → F) : TruthAt rho block.recipe 256 ↔
    (∀ index<255,Square (rho (471+index)) (rho (471+index))) ∧
    fieldBinary (columns.map rho)=rho 6 := by
  constructor
  · intro truth
    constructor
    · intro index bound
      obtain ⟨row,hint,_,found,_⟩:=block.exact_checked index (by omega)
      have value:=truth index (by omega) hint found
      rw [recipes_exact index (by omega) hint found] at value
      change Truth rho (if index<255 then .square [(471+index,1)] [(471+index,1)]
        else .linear (weighted columns 1) [(6,1)]) at value
      rw [if_pos bound] at value
      change Square (eval rho [(471+index,1)]) (eval rho [(471+index,1)]) at value
      simpa only [eval,Int.cast_one,one_mul,add_zero] using value
    · obtain ⟨row,hint,_,found,_⟩:=block.exact_checked 255 (by decide)
      have value:=truth 255 (by decide) hint found
      rw [recipes_exact 255 (by decide) hint found] at value
      change eval rho (weighted columns 1)=eval rho [(6,1)] at value
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using value
  · rintro ⟨bits,reconstruction⟩ index bound hint found
    rw [recipes_exact index bound hint found]
    by_cases before : index<255
    · change Truth rho (if index<255 then .square [(471+index,1)] [(471+index,1)]
        else .linear (weighted columns 1) [(6,1)])
      rw [if_pos before]
      change Square (eval rho [(471+index,1)]) (eval rho [(471+index,1)])
      simpa only [eval,Int.cast_one,one_mul,add_zero] using bits index before
    · have last : index=255 := by omega
      subst index
      change eval rho (weighted columns 1)=eval rho [(6,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.truth_iff
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.truth_iff
theorem meaning_sound (rho : Nat → F) (truth : TruthAt rho block.recipe 256) :
    ∃ n : Nat,n<2^255 ∧ (n : F)=rho 6 := by
  have parts:=(truth_iff rho).mp truth
  have bits : ∀ x∈columns.map rho,Square x x := by
    intro x member
    obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
    change column∈List.range' 471 255 at present
    obtain ⟨offset,offsetBound,offsetSame⟩:=List.mem_range'.mp present
    simp only [one_mul] at offsetSame
    have bounds : 471≤column ∧ column<471+255 := by omega
    have index : column-471<255 := by omega
    have same : 471+(column-471)=column := by omega
    simpa only [same] using parts.1 (column-471) index
  have h:=range_sound (columns.map rho) (rho 6) bits parts.2
  simpa only [columns,List.length_map,List.length_range'] using h

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.meaning_sound
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.meaning_sound
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  writeBits base 471 (encodeBits 255 n)

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.completed
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.completed
theorem completed_truth (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 6=(n : F)) : TruthAt (completed base n) block.recipe 256 := by
  have standard:=writeBits_range_complete base 6 471 255 n bound meaning (by decide)
  apply (truth_iff (completed base n)).mpr
  constructor
  · intro index before
    have member : 471+index∈columns :=
      List.mem_range'.mpr ⟨index,before,by simp only [one_mul]⟩
    have h:=standard (booleanRow (471+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨471+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
  · exact reconstruction_row_sound _ 6 columns
      (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (completed base n) standard


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.completed_truth
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.completed_truth
theorem completed_outside (base : Nat → F) (n column : Nat)
    (outside : column<471 ∨ 471≤column) : completed base n column=base column :=
  writeBits_preserves base 471 (encodeBits 255 n) column (by simpa only [encodeBits_length] using outside)

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.completed_outside
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.completed_outside
theorem completed_fixed (base : Nat → F) (n : Nat) :
    completed base n 0=base 0 ∧ completed base n 1=base 1 ∧ completed base n 2=base 2 ∧
    completed base n copy=base copy ∧ completed base n 6=base 6 :=
  ⟨completed_outside base n 0 (by decide),completed_outside base n 1 (by decide),
    completed_outside base n 2 (by decide),completed_outside base n copy (by decide),
    completed_outside base n 6 (by decide)⟩
variable [CharP F p]

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.completed_fixed
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.completed_fixed
theorem actual_sound (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 256) : ∃ n : Nat,n<2^255 ∧ (n : F)=rho 6 :=
  meaning_sound rho ((CompilerAssertionBlock51.satisfies_iff copy 256 block rho linked).mp satisfied)

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.actual_sound
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.actual_sound
theorem actual_complete (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 6=(n : F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) block.actual 256 := by
  apply (CompilerAssertionBlock51.satisfies_iff copy 256 block (completed base n) _).mpr
  · exact completed_truth base n bound meaning
  · exact (completed_fixed base n).2.2.2.1.trans (linked.trans (completed_fixed base n).1.symm)

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.actual_complete
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.actual_complete
def captureIndex (index : Nat) : Nat := 178377+index

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.captureIndex
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.captureIndex
theorem capture_position (index : Nat) (bound : index<256) : captureIndex index<178633 := by
  change 178377+index<178633
  omega

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.capture_position
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.capture_position
theorem full_position (index : Nat) (bound : index<256) :
    CapturedFullRelation58.rowAt (178377+index)=block.actual index := by
  have sum : 178377+index=177954+(423+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (423+index) (by omega)]
  have h12288 : 423+index<12288 := by omega
  have h4096 : 423+index<4096 := by omega
  have h2048 : 423+index<2048 := by omega
  have h1024 : 423+index<1024 := by omega
  change (if 423+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 423+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 423+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 423+index<1024 then _ else _) = _
  rw [if_pos h1024]
  change (if 423+index<512 then
      (if 423+index<256 then CapturedAssertions50B0000.block.actual (423+index)
        else CapturedAssertions50B0001.block.actual (423+index-256))
    else (if 423+index-512<256 then CapturedAssertions50B0002.block.actual (423+index-512)
      else CapturedAssertions50B0003.block.actual (423+index-512-256))) =
    (if index<89 then CapturedAssertions50B0001.block.actual (167+index)
      else CapturedAssertions50B0002.block.actual (index-89))
  by_cases before : index<89
  · have h512 : 423+index<512 := by omega
    have h256 : ¬423+index<256 := by omega
    have same : 423+index-256=167+index := by omega
    rw [if_pos h512,if_neg h256,if_pos before,same]
  · have h512 : ¬423+index<512 := by omega
    have h256 : 423+index-512<256 := by omega
    have same : 423+index-512=index-89 := by omega
    rw [if_neg h512,if_pos h256,if_neg before,same]


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.full_position
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.full_position
theorem full_complete (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 6=(n:F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) (fun index => CapturedFullRelation58.rowAt (178377+index)) 256 := by
  have done:=actual_complete base n bound meaning linked
  intro index before row found
  change CapturedFullRelation58.rowAt (178377+index)=some row at found
  rw [full_position index before] at found
  exact done index before row found
end ShielddSecurity.CapturedRegistryAssetRange109

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryAssetRange109.full_complete
#print axioms ShielddSecurity.CapturedRegistryAssetRange109.full_complete
