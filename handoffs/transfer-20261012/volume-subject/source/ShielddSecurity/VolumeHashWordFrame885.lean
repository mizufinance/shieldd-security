import ShielddSecurity.ComparisonBorrowFrame324
import ShielddSecurity.VolumeHashAvoid884
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeHashWordFrame885
open Compiler CompilerArithmeticTransport41 WordHints210

open VolumeHashLayout883 (columns plain)
theorem windows_checked : CapturedWordRoot213.words.all (fun entry => columns.all (fun column =>
    decide (column < entry.1.start ∨ entry.1.start+entry.1.width ≤ column))) = true := by decide +kernel

theorem outside_assignments (numbers : Nat → Nat) (column : Nat) (selected : column ∈ VolumeHashLayout883.columns) :
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

theorem plain_unselected (column : Nat) (member : column∈plain) :
    column∉SharedWordWitness221.seedColumns := by
  intro present
  rcases List.mem_append.mp present with boolean|word
  · obtain ⟨slot,known,same⟩ := List.mem_map.mp boolean
    have excluded := List.all_eq_true.mp VolumeHashAvoid884.checked slot known
    have unequal := of_decide_eq_true (List.all_eq_true.mp excluded column member)
    exact unequal same
  · obtain ⟨slot,known,inside⟩ := List.mem_flatMap.mp word
    obtain ⟨entry,entryMember,slotEqual⟩ := List.mem_map.mp known
    subst slot
    have selected := VolumeHashLayout883.plain_columns column member
    have separation := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp windows_checked entry entryMember) column selected)
    obtain ⟨offset,before,same⟩ := List.mem_range'.mp inside
    simp only [Nat.one_mul] at same
    rcases separation with earlier|later <;> omega

variable {F : Type} [Field F] [CharP F p] [DecidableEq F]
theorem flag_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (column : Nat) (selected : column ∈ VolumeHashLayout883.columns)
    (boolean : base column=0 ∨ base column=1)
    (meaning : fallback column=ZeroHintWordFrame303.flags base column) :
    SharedWordWitness221.completed base numbers fallback column=base column := by
  have limits := VolumeHashLayout883.bounds column selected
  have bounds : 3≤column ∧ column<22738 := by omega
  change CapturedFullRelation58.candidate (SharedWordWitness221.seeded base numbers fallback) column = base column
  rw [SharedRegisteredGeneral308.candidate_original _ column bounds.1 bounds.2]
  by_cases seeded : column ∈ SharedWordWitness221.seedColumns
  · change BooleanHints207.seeded base _ _ column=base column
    rw [BooleanHints207.seeded_selected _ _ _ column seeded]
    change BooleanHints207.bitValue (SharedWordFlags220.chosen _ fallback column)=base column
    rw [SharedWordFlags220.chosen_outside _ fallback column (outside_assignments numbers column selected),meaning]
    exact ZeroHintWordFrame303.flags_cast base column boolean
  · exact BooleanHints207.seeded_outside base _ _ column seeded
theorem plain_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (column : Nat) (member : column∈plain) :
    SharedWordWitness221.completed base numbers fallback column=base column := by
  have limits := VolumeHashLayout883.bounds column (VolumeHashLayout883.plain_columns column member)
  change CapturedFullRelation58.candidate (SharedWordWitness221.seeded base numbers fallback) column=base column
  rw [SharedRegisteredGeneral308.candidate_original _ column (by omega) (by omega)]
  exact BooleanHints207.seeded_outside base _ _ column (plain_unselected column member)
end ShielddSecurity.VolumeHashWordFrame885

set_option pp.all true in
#check @ShielddSecurity.VolumeHashWordFrame885.windows_checked
#print axioms ShielddSecurity.VolumeHashWordFrame885.windows_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeHashWordFrame885.outside_assignments
#print axioms ShielddSecurity.VolumeHashWordFrame885.outside_assignments

set_option pp.all true in
#check @ShielddSecurity.VolumeHashWordFrame885.plain_unselected
#print axioms ShielddSecurity.VolumeHashWordFrame885.plain_unselected

set_option pp.all true in
#check @ShielddSecurity.VolumeHashWordFrame885.flag_frame
#print axioms ShielddSecurity.VolumeHashWordFrame885.flag_frame

set_option pp.all true in
#check @ShielddSecurity.VolumeHashWordFrame885.plain_frame
#print axioms ShielddSecurity.VolumeHashWordFrame885.plain_frame
