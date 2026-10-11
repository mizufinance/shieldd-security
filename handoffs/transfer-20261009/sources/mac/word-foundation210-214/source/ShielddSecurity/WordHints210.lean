import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.WordHints210
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
structure Slot where
 position : Nat
 start : Nat
 width : Nat
 value : Nat
def columns (slot : Slot) : List Nat := List.range' slot.start slot.width
def wordRecipe (slot : Slot) : Recipe := .linear (weighted (columns slot) 1) [(slot.value,1)]
def checkSlot (recipes : Nat → Option (Bool × Recipe)) (slot : Slot) : Bool :=
 match recipes slot.position with
 | some hint => BooleanHints207.recipeEqual hint.2 (wordRecipe slot)
 | none => false
theorem checked_slot (recipes : Nat → Option (Bool × Recipe)) (slot : Slot)
 (checked : checkSlot recipes slot=true) :
 ∃ outlined,recipes slot.position=some (outlined,wordRecipe slot) := by
 cases found:recipes slot.position with
 | none => simp only [checkSlot,found,Bool.false_eq_true] at checked
 | some hint =>
   have equal : hint.2=wordRecipe slot :=
     (BooleanHints207.recipeEqual_iff _ _).mp (by simpa only [checkSlot,found] using checked)
   exact ⟨hint.1,by rw [←equal]⟩
def bitSlots (slot : Slot) (first : Nat) : List (Nat × Nat) :=
 (List.range slot.width).map (fun offset => (first+offset,slot.start+offset))
theorem bit_positions (slot : Slot) (first : Nat) (bound : first+slot.width≤22816) :
 ∀ bit∈bitSlots slot first,bit.1<22816 := by
 intro bit member
 obtain ⟨offset,present,rfl⟩:=List.mem_map.mp member
 have before:=List.mem_range.mp present
 change first+offset<22816
 omega
theorem bit_coverage (slot : Slot) (first : Nat) :
 ∀ column∈columns slot,∃ bit∈bitSlots slot first,bit.2=column := by
 intro column member
 obtain ⟨offset,before,equal⟩:=List.mem_range'.mp member
 simp only [Nat.one_mul] at equal
 refine ⟨(first+offset,slot.start+offset),List.mem_map.mpr ⟨offset,List.mem_range.mpr before,rfl⟩,?_⟩
 exact equal.symm
variable {F : Type} [Field F]
theorem word_truth (rho : Nat → F) (slot : Slot) :
 Truth rho (wordRecipe slot) ↔ fieldBinary ((columns slot).map rho)=rho slot.value := by
 change eval rho (weighted (columns slot) 1)=eval rho [(slot.value,1)] ↔ _
 simp only [weighted_eval,Int.cast_one,one_mul,eval,add_zero]
theorem truth_agrees (left right : Nat → F) (slot : Slot)
 (bits : ∀ column∈columns slot,left column=right column)
 (value : left slot.value=right slot.value) :
 Truth left (wordRecipe slot) ↔ Truth right (wordRecipe slot) := by
 rw [word_truth,word_truth,List.map_congr_left bits,value]
def completed (base : Nat → F) (slot : Slot) (n : Nat) : Nat → F :=
 writeBits base slot.start (encodeBits slot.width n)
theorem completed_outside (base : Nat → F) (slot : Slot) (n column : Nat)
 (outside : column<slot.start ∨ slot.start+slot.width≤column) :
 completed base slot n column=base column :=
 writeBits_preserves base slot.start (encodeBits slot.width n) column
   (by simpa only [encodeBits_length] using outside)
theorem completed_truth (base : Nat → F) (slot : Slot) (n : Nat)
 (bound : n<2^slot.width) (meaning : base slot.value=(n : F))
 (outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value) :
 Truth (completed base slot n) (wordRecipe slot) := by
 have satisfied:=writeBits_range_complete base slot.value slot.start slot.width n bound meaning outside
 apply (word_truth _ slot).mpr
 exact reconstruction_row_sound _ slot.value (columns slot)
   (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (completed base slot n) satisfied
theorem candidate_truth (base : Nat → F) (slot : Slot) (n : Nat)
 (bound : n<2^slot.width) (meaning : base slot.value=(n : F))
 (outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738) :
 Truth (CapturedFullRelation58.candidate (completed base slot n)) (wordRecipe slot) := by
 apply (truth_agrees _ (completed base slot n) slot ?_ ?_).mpr
   (completed_truth base slot n bound meaning outside)
 · intro column member
   obtain ⟨offset,before,same⟩:=List.mem_range'.mp member
   simp only [Nat.one_mul] at same
   have known : slot.start≤column ∧ column<slot.start+slot.width := by omega
   have before : column-3<22735 := by omega
   have same : 3+(column-3)=column := by omega
   simpa only [same] using CapturedFullRelation58.candidate_inputs (completed base slot n) (column-3) before
 · have before : slot.value-3<22735 := by omega
   have same : 3+(slot.value-3)=slot.value := by omega
   simpa only [same] using CapturedFullRelation58.candidate_inputs (completed base slot n) (slot.value-3) before
variable [CharP F p]
theorem selected_complete (base : Nat → F) (slot : Slot) (n : Nat)
 (bound : n<2^slot.width) (meaning : base slot.value=(n : F))
 (outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738)
 (position : slot.position<22816)
 (checked : checkSlot CapturedFullAssertions54.recipeAt slot=true) :
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.position)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) := by
 obtain ⟨outlined,matching⟩:=checked_slot _ slot checked
 obtain ⟨row,hint,found,specified,check⟩:=CapturedFullAssertions54.block.exact_checked slot.position position
 have equal : hint=(outlined,wordRecipe slot) := Option.some.inj (specified.symm.trans matching)
 have satisfied : Truth (CapturedFullRelation58.candidate (completed base slot n)) hint.2 := by
   rw [equal]
   exact candidate_truth base slot n bound meaning outside bits_original value_original
 refine ⟨row,?_,(CompilerAssertionBlock51.checked_iff copy row hint check _
   (CapturedFullRelation58.candidate_links (completed base slot n)).2.2).mpr satisfied⟩
 rw [CapturedFullRelation58.assertion_position slot.position position]
 exact found
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (slot : Slot) (position : slot.position<22816)
 (checked : checkSlot CapturedFullAssertions54.recipeAt slot=true)
 (bitSlots : List (Nat × Nat))
 (bitChecks : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt bitSlots=true)
 (bitPositions : ∀ bit∈bitSlots,bit.1<22816)
 (coverage : ∀ column∈columns slot,∃ bit∈bitSlots,bit.2=column) :
 ∃ n : Nat,n<2^slot.width ∧ (n : F)=rho slot.value := by
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2
 obtain ⟨outlined,matching⟩:=checked_slot _ slot checked
 have reconstruction:= (word_truth rho slot).mp (truth slot.position position _ matching)
 have bits : ∀ x∈(columns slot).map rho,Square x x := by
   intro x member
   obtain ⟨column,present,rfl⟩:=List.mem_map.mp member
   obtain ⟨bit,known,equal⟩:=coverage column present
   obtain ⟨flag,found⟩:=BooleanHints207.checked_slot _ bitSlots bitChecks bit known
   have b:=truth bit.1 (bitPositions bit known) _ found
   change Square (eval rho [(bit.2,1)]) (eval rho [(bit.2,1)]) at b
   simpa only [eval,Int.cast_one,one_mul,add_zero,equal] using b
 have meaning:=range_sound ((columns slot).map rho) (rho slot.value) bits reconstruction
 simpa only [columns,List.length_map,List.length_range'] using meaning
end ShielddSecurity.WordHints210

set_option pp.all true in
#check @ShielddSecurity.WordHints210.Slot
#print axioms ShielddSecurity.WordHints210.Slot
set_option pp.all true in
#check @ShielddSecurity.WordHints210.columns
#print axioms ShielddSecurity.WordHints210.columns
set_option pp.all true in
#check @ShielddSecurity.WordHints210.wordRecipe
#print axioms ShielddSecurity.WordHints210.wordRecipe
set_option pp.all true in
#check @ShielddSecurity.WordHints210.checkSlot
#print axioms ShielddSecurity.WordHints210.checkSlot
set_option pp.all true in
#check @ShielddSecurity.WordHints210.checked_slot
#print axioms ShielddSecurity.WordHints210.checked_slot
set_option pp.all true in
#check @ShielddSecurity.WordHints210.bitSlots
#print axioms ShielddSecurity.WordHints210.bitSlots
set_option pp.all true in
#check @ShielddSecurity.WordHints210.bit_positions
#print axioms ShielddSecurity.WordHints210.bit_positions
set_option pp.all true in
#check @ShielddSecurity.WordHints210.bit_coverage
#print axioms ShielddSecurity.WordHints210.bit_coverage
set_option pp.all true in
#check @ShielddSecurity.WordHints210.word_truth
#print axioms ShielddSecurity.WordHints210.word_truth
set_option pp.all true in
#check @ShielddSecurity.WordHints210.truth_agrees
#print axioms ShielddSecurity.WordHints210.truth_agrees
set_option pp.all true in
#check @ShielddSecurity.WordHints210.completed
#print axioms ShielddSecurity.WordHints210.completed
set_option pp.all true in
#check @ShielddSecurity.WordHints210.completed_outside
#print axioms ShielddSecurity.WordHints210.completed_outside
set_option pp.all true in
#check @ShielddSecurity.WordHints210.completed_truth
#print axioms ShielddSecurity.WordHints210.completed_truth
set_option pp.all true in
#check @ShielddSecurity.WordHints210.candidate_truth
#print axioms ShielddSecurity.WordHints210.candidate_truth
set_option pp.all true in
#check @ShielddSecurity.WordHints210.selected_complete
#print axioms ShielddSecurity.WordHints210.selected_complete
set_option pp.all true in
#check @ShielddSecurity.WordHints210.sound
#print axioms ShielddSecurity.WordHints210.sound
