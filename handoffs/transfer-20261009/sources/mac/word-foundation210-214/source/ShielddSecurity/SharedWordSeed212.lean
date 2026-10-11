import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedWordSeed212
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
theorem seeded_map (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat) (slot : Slot)
 (coverage : ∀ column∈columns slot,column∈seedColumns) :
 (columns slot).map (BooleanHints207.seeded base flags seedColumns)=
 ((columns slot).map flags).map (BooleanHints207.bitValue (F := F)) := by
 rw [List.map_map]
 apply List.map_congr_left
 intro column member
 exact BooleanHints207.seeded_selected base flags seedColumns column (coverage column member)
theorem shared_truth_value (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (slot : Slot) (n : Nat) (bound : n<2^slot.width)
 (meaning : BooleanHints207.seeded base flags seedColumns slot.value=(n : F))
 (coverage : ∀ column∈columns slot,column∈seedColumns)
 (encoding : (columns slot).map flags=encodeBits slot.width n) :
 Truth (BooleanHints207.seeded base flags seedColumns) (wordRecipe slot) := by
 apply (word_truth _ slot).mpr
 rw [seeded_map base flags seedColumns slot coverage,encoding]
 change fieldBinary ((encodeBits slot.width n).map (fun b => if b then (1 : F) else 0))=_
 rw [binary_cast,encodeBits_value slot.width n bound]
 exact meaning.symm
theorem shared_truth (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (slot : Slot) (n : Nat) (bound : n<2^slot.width) (meaning : base slot.value=(n : F))
 (coverage : ∀ column∈columns slot,column∈seedColumns)
 (encoding : (columns slot).map flags=encodeBits slot.width n)
 (value_unseeded : slot.value∉seedColumns) :
 Truth (BooleanHints207.seeded base flags seedColumns) (wordRecipe slot) :=
 shared_truth_value base flags seedColumns slot n bound
   ((BooleanHints207.seeded_outside base flags seedColumns slot.value value_unseeded).trans meaning)
   coverage encoding
theorem candidate_transport (base : Nat → F) (slot : Slot)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738) :
 Truth (CapturedFullRelation58.candidate base) (wordRecipe slot) ↔ Truth base (wordRecipe slot) := by
 apply truth_agrees
 · intro column member
   obtain ⟨offset,before,same⟩:=List.mem_range'.mp member
   simp only [Nat.one_mul] at same
   have known : slot.start≤column ∧ column<slot.start+slot.width := by omega
   have before : column-3<22735 := by omega
   have same : 3+(column-3)=column := by omega
   simpa only [same] using CapturedFullRelation58.candidate_inputs base (column-3) before
 · have before : slot.value-3<22735 := by omega
   have same : 3+(slot.value-3)=slot.value := by omega
   simpa only [same] using CapturedFullRelation58.candidate_inputs base (slot.value-3) before
theorem shared_candidate_truth (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (slot : Slot) (n : Nat) (bound : n<2^slot.width) (meaning : base slot.value=(n : F))
 (coverage : ∀ column∈columns slot,column∈seedColumns)
 (encoding : (columns slot).map flags=encodeBits slot.width n)
 (value_unseeded : slot.value∉seedColumns)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738) :
 Truth (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) (wordRecipe slot) :=
 (candidate_transport _ slot bits_original value_original).mpr
   (shared_truth base flags seedColumns slot n bound meaning coverage encoding value_unseeded)
theorem shared_candidate_value (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (slot : Slot) (n : Nat) (bound : n<2^slot.width)
 (meaning : BooleanHints207.seeded base flags seedColumns slot.value=(n : F))
 (coverage : ∀ column∈columns slot,column∈seedColumns)
 (encoding : (columns slot).map flags=encodeBits slot.width n)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738) :
 Truth (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) (wordRecipe slot) :=
 (candidate_transport _ slot bits_original value_original).mpr
   (shared_truth_value base flags seedColumns slot n bound meaning coverage encoding)
variable [CharP F p]
theorem shared_selected (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (slot : Slot) (n : Nat) (bound : n<2^slot.width) (meaning : base slot.value=(n : F))
 (coverage : ∀ column∈columns slot,column∈seedColumns)
 (encoding : (columns slot).map flags=encodeBits slot.width n)
 (value_unseeded : slot.value∉seedColumns)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738)
 (position : slot.position<22816)
 (checked : checkSlot CapturedFullAssertions54.recipeAt slot=true) :
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.position)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) row.a)
        (eval (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) row.b) := by
 obtain ⟨outlined,matching⟩:=checked_slot _ slot checked
 obtain ⟨row,hint,found,specified,check⟩:=CapturedFullAssertions54.block.exact_checked slot.position position
 have equal : hint=(outlined,wordRecipe slot) := Option.some.inj (specified.symm.trans matching)
 have truth : Truth (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) hint.2 := by
   rw [equal]
   exact shared_candidate_truth base flags seedColumns slot n bound meaning coverage encoding value_unseeded bits_original value_original
 refine ⟨row,?_,(CompilerAssertionBlock51.checked_iff copy row hint check _
   (CapturedFullRelation58.candidate_links (BooleanHints207.seeded base flags seedColumns)).2.2).mpr truth⟩
 rw [CapturedFullRelation58.assertion_position slot.position position]
 exact found
theorem shared_selected_value (base : Nat → F) (flags : Nat → Bool) (seedColumns : List Nat)
 (slot : Slot) (n : Nat) (bound : n<2^slot.width) (meaning : BooleanHints207.seeded base flags seedColumns slot.value=(n : F))
 (coverage : ∀ column∈columns slot,column∈seedColumns)
 (encoding : (columns slot).map flags=encodeBits slot.width n)
 (bits_original : 3≤slot.start ∧ slot.start+slot.width≤22738)
 (value_original : 3≤slot.value ∧ slot.value<22738)
 (position : slot.position<22816)
 (checked : checkSlot CapturedFullAssertions54.recipeAt slot=true) :
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.position)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) row.a)
        (eval (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) row.b) := by
 obtain ⟨outlined,matching⟩:=checked_slot _ slot checked
 obtain ⟨row,hint,found,specified,check⟩:=CapturedFullAssertions54.block.exact_checked slot.position position
 have equal : hint=(outlined,wordRecipe slot) := Option.some.inj (specified.symm.trans matching)
 have truth : Truth (CapturedFullRelation58.candidate (BooleanHints207.seeded base flags seedColumns)) hint.2 := by
   rw [equal]
   exact shared_candidate_value base flags seedColumns slot n bound meaning coverage encoding bits_original value_original
 refine ⟨row,?_,(CompilerAssertionBlock51.checked_iff copy row hint check _
   (CapturedFullRelation58.candidate_links (BooleanHints207.seeded base flags seedColumns)).2.2).mpr truth⟩
 rw [CapturedFullRelation58.assertion_position slot.position position]
 exact found
end ShielddSecurity.SharedWordSeed212

set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.seeded_map
#print axioms ShielddSecurity.SharedWordSeed212.seeded_map
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.shared_truth_value
#print axioms ShielddSecurity.SharedWordSeed212.shared_truth_value
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.shared_truth
#print axioms ShielddSecurity.SharedWordSeed212.shared_truth
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.candidate_transport
#print axioms ShielddSecurity.SharedWordSeed212.candidate_transport
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.shared_candidate_truth
#print axioms ShielddSecurity.SharedWordSeed212.shared_candidate_truth
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.shared_candidate_value
#print axioms ShielddSecurity.SharedWordSeed212.shared_candidate_value
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.shared_selected
#print axioms ShielddSecurity.SharedWordSeed212.shared_selected
set_option pp.all true in
#check @ShielddSecurity.SharedWordSeed212.shared_selected_value
#print axioms ShielddSecurity.SharedWordSeed212.shared_selected_value
