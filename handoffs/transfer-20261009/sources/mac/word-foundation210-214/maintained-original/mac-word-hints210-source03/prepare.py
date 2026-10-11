from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-word-hints210-source03'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source preparation');require(not S.exists(),'new immutable source')
body='''import ShielddSecurity.BooleanHints207
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
'''
names=['Slot','columns','wordRecipe','checkSlot','checked_slot','bitSlots','bit_positions','bit_coverage','word_truth','truth_agrees','completed','completed_outside','completed_truth','candidate_truth','selected_complete','sound']
inputs=[W/'mac-boolean-hints207-source05/source-root/ShielddSecurity/BooleanHints207.lean',W/'mac-transfer-pilot01/project/ShielddSecurity/Rows.lean',W/'mac-assertion-block51-source02/source-root/ShielddSecurity/CompilerAssertionBlock51.lean',W/'mac-full-captured-relation58-source02/source-root/ShielddSecurity/CapturedFullRelation58.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-boolean-root209-source02/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'WordHints210':dict(body=body,names=names)},inputs={str(p):pin(p)for p in inputs},scope='SOURCE_ONLY_UNRUN16 explicit audits. Generic exact finite recipe check, bounded independent natural bit-word constructor and arbitrary full-relation recovery. Candidate transport only original bit/value columns with concrete finite bounds. No word/hash/row-truth premises; natural bound and original value meaning are explicit legal input interpretation obligations. Overlap/word consistency/actual66 instances/full legal witness/native remain OPEN.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(stage=str(S),planned_audits=len(names))))
