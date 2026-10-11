import ShielddSecurity.CapturedRegistryValueRange97Data
import ShielddSecurity.CapturedGlobalSubgroup90
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryValueRange97
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
theorem truth_iff (rho : Nat → F) : TruthAt rho block.recipe 256 ↔
    (∀ index<255,Square (rho (216+index)) (rho (216+index))) ∧
    fieldBinary (columns.map rho)=rho 11 := by
  constructor
  · intro truth
    constructor
    · intro index bound
      obtain ⟨row,hint,_,found,_⟩:=block.exact_checked index (by omega)
      have value:=truth index (by omega) hint found
      rw [recipes_exact index (by omega) hint found] at value
      change Truth rho (if index<255 then .square [(216+index,1)] [(216+index,1)]
        else .linear (weighted columns 1) [(11,1)]) at value
      rw [if_pos bound] at value
      change Square (eval rho [(216+index,1)]) (eval rho [(216+index,1)]) at value
      simpa only [eval,Int.cast_one,one_mul,add_zero] using value
    · obtain ⟨row,hint,_,found,_⟩:=block.exact_checked 255 (by decide)
      have value:=truth 255 (by decide) hint found
      rw [recipes_exact 255 (by decide) hint found] at value
      change eval rho (weighted columns 1)=eval rho [(11,1)] at value
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using value
  · rintro ⟨bits,reconstruction⟩ index bound hint found
    rw [recipes_exact index bound hint found]
    by_cases before : index<255
    · change Truth rho (if index<255 then .square [(216+index,1)] [(216+index,1)]
        else .linear (weighted columns 1) [(11,1)])
      rw [if_pos before]
      change Square (eval rho [(216+index,1)]) (eval rho [(216+index,1)])
      simpa only [eval,Int.cast_one,one_mul,add_zero] using bits index before
    · have last : index=255 := by omega
      subst index
      change eval rho (weighted columns 1)=eval rho [(11,1)]
      simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using reconstruction

theorem meaning_sound (rho : Nat → F) (truth : TruthAt rho block.recipe 256) :
    ∃ n : Nat,n<2^255 ∧ (n : F)=rho 11 := by
  have parts:=(truth_iff rho).mp truth
  have bits : ∀ x∈columns.map rho,Square x x := by
    intro x member
    obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
    change column∈List.range' 216 255 at present
    obtain ⟨offset,offsetBound,offsetSame⟩:=List.mem_range'.mp present
    simp only [one_mul] at offsetSame
    have bounds : 216≤column ∧ column<216+255 := by omega
    have index : column-216<255 := by omega
    have same : 216+(column-216)=column := by omega
    simpa only [same] using parts.1 (column-216) index
  have h:=range_sound (columns.map rho) (rho 11) bits parts.2
  simpa only [columns,List.length_map,List.length_range'] using h
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  writeBits base 216 (encodeBits 255 n)
theorem completed_truth (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 11=(n : F)) : TruthAt (completed base n) block.recipe 256 := by
  have standard:=writeBits_range_complete base 11 216 255 n bound meaning (by decide)
  apply (truth_iff (completed base n)).mpr
  constructor
  · intro index before
    have member : 216+index∈columns :=
      List.mem_range'.mpr ⟨index,before,by simp only [one_mul]⟩
    have h:=standard (booleanRow (216+index))
      (List.mem_append_left _ (List.mem_map.mpr ⟨216+index,member,rfl⟩))
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using h
  · exact reconstruction_row_sound _ 11 columns
      (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (completed base n) standard

theorem completed_outside (base : Nat → F) (n column : Nat)
    (outside : column<216 ∨ 471≤column) : completed base n column=base column :=
  writeBits_preserves base 216 (encodeBits 255 n) column (by simpa only [encodeBits_length] using outside)
theorem completed_fixed (base : Nat → F) (n : Nat) :
    completed base n 0=base 0 ∧ completed base n 1=base 1 ∧ completed base n 2=base 2 ∧
    completed base n copy=base copy ∧ completed base n 11=base 11 :=
  ⟨completed_outside base n 0 (by decide),completed_outside base n 1 (by decide),
    completed_outside base n 2 (by decide),completed_outside base n copy (by decide),
    completed_outside base n 11 (by decide)⟩
variable [CharP F p]
theorem actual_sound (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 256) : ∃ n : Nat,n<2^255 ∧ (n : F)=rho 11 :=
  meaning_sound rho ((CompilerAssertionBlock51.satisfies_iff copy 256 block rho linked).mp satisfied)
theorem actual_complete (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 11=(n : F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) block.actual 256 := by
  apply (CompilerAssertionBlock51.satisfies_iff copy 256 block (completed base n) _).mpr
  · exact completed_truth base n bound meaning
  · exact (completed_fixed base n).2.2.2.1.trans (linked.trans (completed_fixed base n).1.symm)
def captureIndex (index : Nat) : Nat := 178119+index
theorem capture_position (index : Nat) (bound : index<256) : captureIndex index<178375 := by
  change 178119+index<178375
  omega
theorem full_position (index : Nat) (bound : index<256) :
    CapturedFullRelation58.rowAt (178119+index)=block.actual index := by
  have sum : 178119+index=177954+(165+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (165+index) (by omega)]
  have h12288 : 165+index<12288 := by omega
  have h4096 : 165+index<4096 := by omega
  have h2048 : 165+index<2048 := by omega
  have h1024 : 165+index<1024 := by omega
  have h512 : 165+index<512 := by omega
  by_cases before : index<91
  · have h256 : 165+index<256 := by omega
    simp only [CapturedFullAssertions54.rowAt,CapturedFullAssertions54.block,CapturedAssertions54G00.block,
      CompilerAssertionBlock51.append,block,h12288,h4096,h2048,h1024,h512,h256,before,if_true]
  · have h256 : ¬165+index<256 := by omega
    have same : 165+index-256=index-91 := by omega
    simp only [CapturedFullAssertions54.rowAt,CapturedFullAssertions54.block,CapturedAssertions54G00.block,
      CompilerAssertionBlock51.append,block,h12288,h4096,h2048,h1024,h512,h256,before,if_true,if_false,same]
theorem full_complete (base : Nat → F) (n : Nat) (bound : n<2^255)
    (meaning : base 11=(n:F)) (linked : base copy=base 0) :
    SatisfiesAt (completed base n) (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 := by
  have done:=actual_complete base n bound meaning linked
  intro index before row found
  rw [full_position index before] at found
  exact done index before row found
end ShielddSecurity.CapturedRegistryValueRange97
