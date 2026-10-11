import ShielddSecurity.CapturedWordRoot213
import ShielddSecurity.CapturedBooleanRoot209
import ShielddSecurity.SharedWordFlags220
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedWordWitness221
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
def wordSlots : List Slot := CapturedWordRoot213.words.map Prod.fst
def seedColumns : List Nat := CapturedBooleanRoot209.columns ++ wordSlots.flatMap WordHints210.columns
def bits (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → Bool :=
 SharedWordFlags220.flags wordSlots numbers fallback
theorem word_coverage (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words)
 (column : Nat) (present : column∈WordHints210.columns entry.1) : column∈seedColumns :=
 List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry.1,List.mem_map.mpr ⟨entry,member,rfl⟩,present⟩)
theorem boolean_coverage (slot : Nat × Nat) (member : slot∈CapturedBooleanRoot209.slots) :
 slot.2∈seedColumns := List.mem_append_left _ (CapturedBooleanRoot209.coverage slot member)
theorem columns_outside (column : Nat) (outside : column<3 ∨ 22738≤column) : column∉seedColumns := by
 intro member
 rcases List.mem_append.mp member with boolean|word
 · exact CapturedBooleanRoot209.columns_outside column outside boolean
 · obtain ⟨slot,known,present⟩:=List.mem_flatMap.mp word
   obtain ⟨entry,member,equal⟩:=List.mem_map.mp known
   subst slot
   have bound:=(CapturedWordRoot213.originals entry member).1
   obtain ⟨offset,before,equal⟩:=List.mem_range'.mp present
   simp only [Nat.one_mul] at equal
   omega
theorem encoded (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments wordSlots numbers))
 (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words) :
 (WordHints210.columns entry.1).map (bits numbers fallback)=encodeBits entry.1.width (numbers entry.1.value) :=
 SharedWordFlags220.encoded wordSlots numbers fallback coherent entry.1
   (List.mem_map.mpr ⟨entry,member,rfl⟩)
variable {F : Type} [Field F]
noncomputable def seeded (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → F :=
 BooleanHints207.seeded base (bits numbers fallback) seedColumns
theorem seeded_fixed (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 seeded base numbers fallback 0=base 0 ∧ seeded base numbers fallback 1=base 1 ∧
 seeded base numbers fallback 2=base 2 ∧ seeded base numbers fallback copy=base copy :=
 ⟨BooleanHints207.seeded_outside base _ seedColumns 0 (columns_outside 0 (by decide)),
 BooleanHints207.seeded_outside base _ seedColumns 1 (columns_outside 1 (by decide)),
 BooleanHints207.seeded_outside base _ seedColumns 2 (columns_outside 2 (by decide)),
 BooleanHints207.seeded_outside base _ seedColumns copy (columns_outside copy (by decide))⟩
variable [CharP F p]
noncomputable def completed (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → F :=
 CapturedFullRelation58.candidate (seeded base numbers fallback)
theorem arithmetic (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 CompilerArithmeticBlock44.SatisfiesAt (completed base numbers fallback) CapturedFullArithmetic52.rowAt 177954 :=
 CapturedFullRelation58.candidate_arithmetic (seeded base numbers fallback)
theorem boolean_rows (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 ∀ slot∈CapturedBooleanRoot209.slots,∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (completed base numbers fallback) row.a) (eval (completed base numbers fallback) row.b) :=
 BooleanHints207.candidate_selected base (bits numbers fallback) seedColumns CapturedBooleanRoot209.slots
 CapturedBooleanRoot209.checked CapturedBooleanRoot209.originals boolean_coverage CapturedBooleanRoot209.positions
theorem word_rows (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments wordSlots numbers))
 (bounded : ∀ entry∈CapturedWordRoot213.words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈CapturedWordRoot213.words,seeded base numbers fallback entry.1.value=(numbers entry.1.value : F)) :
 ∀ entry∈CapturedWordRoot213.words,∃ row,CapturedFullRelation58.rowAt (177954+entry.1.position)=some row ∧
 Square (eval (completed base numbers fallback) row.a) (eval (completed base numbers fallback) row.b) :=
 CapturedWordRoot213.shared_constructor base (bits numbers fallback) seedColumns numbers
 bounded meanings word_coverage (encoded numbers fallback coherent)
theorem unselected_input (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (input : Nat) (bound : input<22735) (outside : 3+input∉seedColumns) :
 completed base numbers fallback (3+input)=base (3+input) :=
 (CapturedFullRelation58.candidate_inputs (seeded base numbers fallback) input bound).trans
 (BooleanHints207.seeded_outside base _ seedColumns (3+input) outside)
theorem links (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
 completed base numbers fallback 1=completed base numbers fallback 22737 ∧
 completed base numbers fallback 2=completed base numbers fallback 9 ∧
 completed base numbers fallback copy=completed base numbers fallback 0 :=
 CapturedFullRelation58.candidate_links (seeded base numbers fallback)
end ShielddSecurity.SharedWordWitness221

set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.wordSlots
#print axioms ShielddSecurity.SharedWordWitness221.wordSlots
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.seedColumns
#print axioms ShielddSecurity.SharedWordWitness221.seedColumns
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.bits
#print axioms ShielddSecurity.SharedWordWitness221.bits
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.word_coverage
#print axioms ShielddSecurity.SharedWordWitness221.word_coverage
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.boolean_coverage
#print axioms ShielddSecurity.SharedWordWitness221.boolean_coverage
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.columns_outside
#print axioms ShielddSecurity.SharedWordWitness221.columns_outside
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.encoded
#print axioms ShielddSecurity.SharedWordWitness221.encoded
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.seeded
#print axioms ShielddSecurity.SharedWordWitness221.seeded
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.seeded_fixed
#print axioms ShielddSecurity.SharedWordWitness221.seeded_fixed
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.completed
#print axioms ShielddSecurity.SharedWordWitness221.completed
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.arithmetic
#print axioms ShielddSecurity.SharedWordWitness221.arithmetic
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.boolean_rows
#print axioms ShielddSecurity.SharedWordWitness221.boolean_rows
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.word_rows
#print axioms ShielddSecurity.SharedWordWitness221.word_rows
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.unselected_input
#print axioms ShielddSecurity.SharedWordWitness221.unselected_input
set_option pp.all true in
#check @ShielddSecurity.SharedWordWitness221.links
#print axioms ShielddSecurity.SharedWordWitness221.links
