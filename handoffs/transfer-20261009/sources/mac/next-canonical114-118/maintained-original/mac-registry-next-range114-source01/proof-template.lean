import ShielddSecurity.CapturedRegistryNextRange114Data
import ShielddSecurity.CapturedGlobalSubgroup90
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryNextRange114
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
theorem truth_iff (rho : Nat → F) : TruthAt rho block.recipe 256 ↔
    (∀ index<255,Square (rho (726+index)) (rho (726+index))) ∧
    fieldBinary (columns.map rho)=rho 13 := by
  constructor
  · intro truth
    constructor
    · intro index bound
      obtain ⟨row,hint,_,found,_⟩:=block.exact_checked index (by omega)
      have value:=truth index (by omega) hint found
      rw [recipes_exact index (by omega) hint found] at value
      change Truth rho (if index<255 then .square [(726+index,1)] [(726+index,1)]
        else .linear (weighted columns 1) [(13,1)]) at value
      rw [if_pos bound] at value
      change Square (eval rho [(726+index,1)]) (eval rho [(726+index,1)]) at value
      simpa only [eval,Int.cast_one,one_mul,add_zero] using value
    · obtain ⟨row,hint,_,found,_⟩:=block.exact_checked 255 (by decide)
      have value:=truth 255 (by decide) hint found
      rw [recipes_exact 255 (by decide) hint found] at value
      change eval rho (weighted columns 1)=eval rho [(13,1)] at value
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using value
  · rintro ⟨bits,reconstruction⟩ index bound hint found
    rw [recipes_exact index bound hint found]
    by_cases before : index<255
    · change Truth rho (if index<255 then .square [(726+index,1)] [(726+index,1)]
        else .linear (weighted columns 1) [(13,1)])
      rw [if_pos before]
      change Square (eval rho [(726+index,1)]) (eval rho [(726+index,1)])
      simpa only [eval,Int.cast_one,one_mul,add_zero] using bits index before
    · have last : index=255 := by omega
      subst index
      change eval rho (weighted columns 1)=eval rho [(13,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction

theorem meaning_sound (rho : Nat → F) (truth : TruthAt rho block.recipe 256) :
    ∃ n : Nat,n<2^255 ∧ (n : F)=rho 13 := by
  have parts:=(truth_iff rho).mp truth
  have bits : ∀ x∈columns.map rho,Square x x := by
    intro x member
    obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
    change column∈List.range' 726 255 at present
    obtain ⟨offset,offsetBound,offsetSame⟩:=List.mem_range'.mp present
    simp only [one_mul] at offsetSame
    have bounds : 726≤column ∧ column<726+255 := by omega
    have index : column-726<255 := by omega
    have same : 726+(column-726)=column := by omega
    simpa only [same] using parts.1 (column-726) index
  have h:=range_sound (columns.map rho) (rho 13) bits parts.2
  simpa only [columns,List.length_map,List.length_range'] using h
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  writeBits base 726 (encodeBits 255 n)
theorem completed_truth (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 13=(n : F)) : TruthAt (completed base n) block.recipe 256 := by
  have standard:=writeBits_range_complete base 13 726 255 n bound meaning (by decide)
  apply (truth_iff (completed base n)).mpr
  constructor
  · intro index before
    have member : 726+index∈columns :=
      List.mem_range'.mpr ⟨index,before,by simp only [one_mul]⟩
    have h:=standard (booleanRow (726+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨726+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
  · exact reconstruction_row_sound _ 13 columns
      (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (completed base n) standard

theorem completed_outside (base : Nat → F) (n column : Nat)
    (outside : column<726 ∨ 981≤column) : completed base n column=base column :=
  writeBits_preserves base 726 (encodeBits 255 n) column (by simpa only [encodeBits_length] using outside)
theorem completed_fixed (base : Nat → F) (n : Nat) :
    completed base n 0=base 0 ∧ completed base n 1=base 1 ∧ completed base n 2=base 2 ∧
    completed base n copy=base copy ∧ completed base n 13=base 13 :=
  ⟨completed_outside base n 0 (by decide),completed_outside base n 1 (by decide),
    completed_outside base n 2 (by decide),completed_outside base n copy (by decide),
    completed_outside base n 13 (by decide)⟩
variable [CharP F p]
theorem actual_sound (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 256) : ∃ n : Nat,n<2^255 ∧ (n : F)=rho 13 :=
  meaning_sound rho ((CompilerAssertionBlock51.satisfies_iff copy 256 block rho linked).mp satisfied)
theorem actual_complete (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 13=(n : F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) block.actual 256 := by
  apply (CompilerAssertionBlock51.satisfies_iff copy 256 block (completed base n) _).mpr
  · exact completed_truth base n bound meaning
  · exact (completed_fixed base n).2.2.2.1.trans (linked.trans (completed_fixed base n).1.symm)
def captureIndex (index : Nat) : Nat := 178635+index
theorem capture_position (index : Nat) (bound : index<256) : captureIndex index<178891 := by
  change 178635+index<178891
  omega
theorem full_position (index : Nat) (bound : index<256) :
    CapturedFullRelation58.rowAt (178635+index)=block.actual index := by
  have sum : 178635+index=177954+(681+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (681+index) (by omega)]
  have h12288 : 681+index<12288 := by omega
  have h4096 : 681+index<4096 := by omega
  have h2048 : 681+index<2048 := by omega
  have h1024 : 681+index<1024 := by omega
  change (if 681+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 681+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 681+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 681+index<1024 then _ else _) = _
  rw [if_pos h1024]
  change (if 681+index<512 then _ else _) = _
  rw [if_neg (show ¬681+index<512 by omega)]
  change (if 681+index-512<256 then CapturedAssertions50B0002.block.actual (681+index-512)
    else CapturedAssertions50B0003.block.actual (681+index-512-256)) =
    (if index<87 then CapturedAssertions50B0002.block.actual (169+index)
      else CapturedAssertions50B0003.block.actual (index-87))
  by_cases before : index<87
  · have h256 : 681+index-512<256 := by omega
    have same : 681+index-512=169+index := by omega
    rw [if_pos h256,if_pos before,same]
  · have h256 : ¬681+index-512<256 := by omega
    have same : 681+index-512-256=index-87 := by omega
    rw [if_neg h256,if_neg before,same]

theorem full_complete (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 13=(n:F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) (fun index => CapturedFullRelation58.rowAt (178635+index)) 256 := by
  have done:=actual_complete base n bound meaning linked
  intro index before row found
  change CapturedFullRelation58.rowAt (178635+index)=some row at found
  rw [full_position index before] at found
  exact done index before row found
end ShielddSecurity.CapturedRegistryNextRange114
