import ShielddSecurity.LegalWordNormalization272
import ShielddSecurity.CapturedBooleanRoot209
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalAliasMeanings276
open WordHints210 LegalWordNormalization272
theorem selected0 : 9059∈SharedWordWitness221.seedColumns :=
 SharedWordWitness221.boolean_coverage (8831,9059) (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (by decide +kernel : (8831,9059)∈CapturedBooleanSlots208B0034.slots)))))))
theorem selected1 : 10591∈SharedWordWitness221.seedColumns :=
 SharedWordWitness221.boolean_coverage (10371,10591) (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (by decide +kernel : (10371,10591)∈CapturedBooleanSlots208B0040.slots)))))))
theorem selected2 : 20935∈SharedWordWitness221.seedColumns :=
 SharedWordWitness221.boolean_coverage (20996,20935) (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (by decide +kernel : (20996,20935)∈CapturedBooleanSlots208B0082.slots)))))))
theorem selected (column : Nat) (selectedAlias : Alias column) : column∈SharedWordWitness221.seedColumns := by
 rcases selectedAlias with first|second|third
 · subst column;exact selected0
 · subst column;exact selected1
 · subst column;exact selected2
def Separate (slot : Slot) (column : Nat) : Prop := column<slot.start ∨ slot.start+slot.width≤column
instance separateDecidable (slot : Slot) (column : Nat) : Decidable (Separate slot column) := inferInstanceAs (Decidable (column<slot.start ∨ slot.start+slot.width≤column))
theorem separate_checked : CapturedWordRoot213.words.all (fun entry =>
 decide (Separate entry.1 9059 ∧ Separate entry.1 10591 ∧ Separate entry.1 20935))=true := by decide +kernel
theorem separate (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words)
 (column : Nat) (selectedAlias : Alias column) : Separate entry.1 column := by
 have facts := of_decide_eq_true ((List.all_eq_true.mp separate_checked) entry member)
 rcases selectedAlias with first|second|third
 · subst column;exact facts.1
 · subst column;exact facts.2.1
 · subst column;exact facts.2.2
theorem columns_outside (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words)
 (column : Nat) (selectedAlias : Alias column) : column∉columns entry.1 := by
 intro present
 obtain ⟨offset,before,equal⟩ := List.mem_range'.mp present
 have facts := separate entry member column selectedAlias
 simp only [Nat.one_mul] at equal
 rcases facts with earlier|later <;> omega
theorem assignments_outside (numbers : Nat → Nat) (column : Nat) (selectedAlias : Alias column) :
 column∉(SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers).map Prod.fst := by
 intro present
 obtain ⟨pair,known,equal⟩ := List.mem_map.mp present
 obtain ⟨slot,slotMember,pairMember⟩ := List.mem_flatMap.mp known
 obtain ⟨entry,entryMember,slotEqual⟩ := List.mem_map.mp slotMember
 subst slot
 have inColumns := (List.of_mem_zip pairMember).1
 exact columns_outside entry entryMember column selectedAlias (equal ▸ inColumns)
def fallback (numbers : Nat → Nat) (old : Nat → Bool) (column : Nat) : Bool :=
 if column=9059 then decide (numbers 9061%2=1)
 else if column=10591 then decide (numbers 10593%2=1)
 else if column=20935 then decide (numbers 20937%2=1) else old column
theorem fallback_fixed (numbers : Nat → Nat) (old : Nat → Bool) (column : Nat)
 (outside : ¬Alias column) : fallback numbers old column=old column := by
 have first : column≠9059 := fun equal => outside (Or.inl equal)
 have second : column≠10591 := fun equal => outside (Or.inr (Or.inl equal))
 have third : column≠20935 := fun equal => outside (Or.inr (Or.inr equal))
 simp only [fallback,if_neg first,if_neg second,if_neg third]
variable {F : Type} [Field F]
theorem bit_parity (number : Nat) : BooleanHints207.bitValue (decide (number%2=1))=((number%2:Nat):F) := by
 by_cases one : number%2=1
 · simp [BooleanHints207.bitValue,one]
 · have zero : number%2=0 := by have bound:=Nat.mod_lt number (by decide : 0<2);omega
   simp [BooleanHints207.bitValue,zero]
theorem fallback_meaning (numbers : Nat → Nat) (old : Nat → Bool) (column : Nat)
 (selectedAlias : Alias column) : BooleanHints207.bitValue (fallback numbers old column)=(normalized numbers column:F) := by
 rcases selectedAlias with first|second|third
 · subst column;simpa [fallback,normalized] using (bit_parity (F:=F) (numbers 9061))
 · subst column;simpa [fallback,normalized] using (bit_parity (F:=F) (numbers 10593))
 · subst column;simpa [fallback,normalized] using (bit_parity (F:=F) (numbers 20937))
theorem seeded_meaning (base : Nat → F) (numbers : Nat → Nat) (old : Nat → Bool) (column : Nat)
 (selectedAlias : Alias column) :
 SharedWordWitness221.seeded base (normalized numbers) (fallback numbers old) column=(normalized numbers column:F) := by
 change BooleanHints207.seeded base (SharedWordWitness221.bits (normalized numbers) (fallback numbers old))
  SharedWordWitness221.seedColumns column=(normalized numbers column:F)
 rw [BooleanHints207.seeded_selected _ _ _ column (selected column selectedAlias)]
 change BooleanHints207.bitValue (SharedWordFlags220.chosen
  (SharedWordFlags220.assignments SharedWordWitness221.wordSlots (normalized numbers))
  (fallback numbers old) column)=_
 rw [SharedWordFlags220.chosen_outside _ _ column (assignments_outside _ column selectedAlias)]
 exact fallback_meaning numbers old column selectedAlias
theorem all_meanings (base : Nat → F) (numbers : Nat → Nat) (old : Nat → Bool)
 (other : ∀ entry∈CapturedWordRoot213.words,¬Alias entry.1.value →
  SharedWordWitness221.seeded base (normalized numbers) (fallback numbers old) entry.1.value=(normalized numbers entry.1.value:F)) :
 ∀ entry∈CapturedWordRoot213.words,SharedWordWitness221.seeded base (normalized numbers) (fallback numbers old) entry.1.value=(normalized numbers entry.1.value:F) := by
 intro entry member
 by_cases selectedAlias : Alias entry.1.value
 · exact seeded_meaning base numbers old entry.1.value selectedAlias
 · exact other entry member selectedAlias
end ShielddSecurity.LegalAliasMeanings276

set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.selected0
#print axioms ShielddSecurity.LegalAliasMeanings276.selected0
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.selected1
#print axioms ShielddSecurity.LegalAliasMeanings276.selected1
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.selected2
#print axioms ShielddSecurity.LegalAliasMeanings276.selected2
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.selected
#print axioms ShielddSecurity.LegalAliasMeanings276.selected
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.Separate
#print axioms ShielddSecurity.LegalAliasMeanings276.Separate
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.separateDecidable
#print axioms ShielddSecurity.LegalAliasMeanings276.separateDecidable
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.separate_checked
#print axioms ShielddSecurity.LegalAliasMeanings276.separate_checked
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.separate
#print axioms ShielddSecurity.LegalAliasMeanings276.separate
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.columns_outside
#print axioms ShielddSecurity.LegalAliasMeanings276.columns_outside
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.assignments_outside
#print axioms ShielddSecurity.LegalAliasMeanings276.assignments_outside
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.fallback
#print axioms ShielddSecurity.LegalAliasMeanings276.fallback
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.fallback_fixed
#print axioms ShielddSecurity.LegalAliasMeanings276.fallback_fixed
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.bit_parity
#print axioms ShielddSecurity.LegalAliasMeanings276.bit_parity
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.fallback_meaning
#print axioms ShielddSecurity.LegalAliasMeanings276.fallback_meaning
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.seeded_meaning
#print axioms ShielddSecurity.LegalAliasMeanings276.seeded_meaning
set_option pp.all true in
#check @ShielddSecurity.LegalAliasMeanings276.all_meanings
#print axioms ShielddSecurity.LegalAliasMeanings276.all_meanings
