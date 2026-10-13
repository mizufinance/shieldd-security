import ShielddSecurity.ComparisonBorrowFrame324
import ShielddSecurity.HighZeroInverseAvoid331
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroHintFrame330
open Compiler CompilerArithmeticTransport41 WordHints210

def columns : List Nat := [1110,1111,1371,1372]
theorem windows_checked : CapturedWordRoot213.words.all (fun entry => columns.all (fun column =>
    decide (column < entry.1.start ∨ entry.1.start+entry.1.width ≤ column))) = true := by decide +kernel

theorem outside_assignments (numbers : Nat → Nat) (column : Nat) (selected : column ∈ columns) :
    column ∉ (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers).map Prod.fst := by
  intro member
  obtain ⟨pair,known,equal⟩ := List.mem_map.mp member
  obtain ⟨slot,slotMember,pairMember⟩ := List.mem_flatMap.mp known
  obtain ⟨entry,entryMember,slotEqual⟩ := List.mem_map.mp slotMember
  subst slot
  have inside := (List.of_mem_zip pairMember).1
  have separation := of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp windows_checked) entry entryMember)) column selected)
  rcases pair with ⟨field,bit⟩
  change field=column at equal
  rw [equal] at inside
  obtain ⟨offset,before,same⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at same
  rcases separation with earlier | later <;> omega

theorem boolean_inverse_checked : CapturedBooleanRoot209.slots.all (fun slot =>
    decide (slot.2≠1111 ∧ slot.2≠1372)) = true := HighZeroInverseAvoid331.checked

theorem inverse_unselected (column : Nat) (inverse : column=1111 ∨ column=1372) :
    column ∉ SharedWordWitness221.seedColumns := by
  intro member
  rcases List.mem_append.mp member with boolean | word
  · obtain ⟨slot,known,same⟩ := List.mem_map.mp boolean
    have excluded := of_decide_eq_true ((List.all_eq_true.mp boolean_inverse_checked) slot known)
    rcases inverse with first | second <;> omega
  · obtain ⟨slot,known,inside⟩ := List.mem_flatMap.mp word
    obtain ⟨entry,entryMember,slotEqual⟩ := List.mem_map.mp known
    subst slot
    have selected : column ∈ columns := by rcases inverse with rfl | rfl <;> decide
    have separation := of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp windows_checked) entry entryMember)) column selected)
    obtain ⟨offset,before,same⟩ := List.mem_range'.mp inside
    simp only [Nat.one_mul] at same
    rcases separation with earlier | later <;> omega

variable {F : Type} [Field F] [CharP F p] [DecidableEq F]
theorem flag_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (column : Nat) (selected : column ∈ columns)
    (boolean : base column=0 ∨ base column=1)
    (meaning : fallback column=ZeroHintWordFrame303.flags base column) :
    SharedWordWitness221.completed base numbers fallback column=base column := by
  have bounds : 3 ≤ column ∧ column < 22738 := by
    simp only [columns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> omega
  change CapturedFullRelation58.candidate (SharedWordWitness221.seeded base numbers fallback) column = base column
  rw [SharedRegisteredGeneral308.candidate_original _ column bounds.1 bounds.2]
  by_cases seeded : column ∈ SharedWordWitness221.seedColumns
  · change BooleanHints207.seeded base _ _ column=base column
    rw [BooleanHints207.seeded_selected _ _ _ column seeded]
    change BooleanHints207.bitValue (SharedWordFlags220.chosen _ fallback column)=base column
    rw [SharedWordFlags220.chosen_outside _ fallback column (outside_assignments numbers column selected),meaning]
    exact ZeroHintWordFrame303.flags_cast base column boolean
  · exact BooleanHints207.seeded_outside base _ _ column seeded
end ShielddSecurity.HighZeroHintFrame330

set_option pp.all true in
#check @ShielddSecurity.HighZeroHintFrame330.columns
#print axioms ShielddSecurity.HighZeroHintFrame330.columns

set_option pp.all true in
#check @ShielddSecurity.HighZeroHintFrame330.windows_checked
#print axioms ShielddSecurity.HighZeroHintFrame330.windows_checked

set_option pp.all true in
#check @ShielddSecurity.HighZeroHintFrame330.outside_assignments
#print axioms ShielddSecurity.HighZeroHintFrame330.outside_assignments

set_option pp.all true in
#check @ShielddSecurity.HighZeroHintFrame330.boolean_inverse_checked
#print axioms ShielddSecurity.HighZeroHintFrame330.boolean_inverse_checked

set_option pp.all true in
#check @ShielddSecurity.HighZeroHintFrame330.inverse_unselected
#print axioms ShielddSecurity.HighZeroHintFrame330.inverse_unselected

set_option pp.all true in
#check @ShielddSecurity.HighZeroHintFrame330.flag_frame
#print axioms ShielddSecurity.HighZeroHintFrame330.flag_frame
