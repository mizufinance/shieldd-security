import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.CapturedRegisteredHints72
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ZeroHintWordFrame303
open WordHints210 SharedWordFlags220

theorem checked_windows : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.start + entry.1.width ≤ 113 ∨ 135 ≤ entry.1.start)) = true := by decide +kernel

theorem outside_window (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (column : Nat) (lower : 113 ≤ column) (upper : column < 135) :
    column ∉ columns entry.1 := by
  intro inside
  have separated := of_decide_eq_true ((List.all_eq_true.mp checked_windows) entry member)
  obtain ⟨offset, before, equal⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at equal
  rcases separated with earlier | later <;> omega

theorem assignments_outside (numbers : Nat → Nat) (column : Nat)
    (lower : 113 ≤ column) (upper : column < 135) :
    column ∉ (assignments SharedWordWitness221.wordSlots numbers).map Prod.fst := by
  intro member
  obtain ⟨pair, selected, same⟩ := List.mem_map.mp member
  obtain ⟨slot, known, paired⟩ := List.mem_flatMap.mp selected
  obtain ⟨entry, entryKnown, slotEqual⟩ := List.mem_map.mp known
  subst slot
  rcases pair with ⟨field, bit⟩
  have inside := (List.of_mem_zip paired).1
  exact outside_window entry entryKnown column lower upper (same ▸ inside)

theorem bits_outside (numbers : Nat → Nat) (fallback : Nat → Bool) (column : Nat)
    (lower : 113 ≤ column) (upper : column < 135) :
    SharedWordWitness221.bits numbers fallback column = fallback column :=
  chosen_outside _ fallback column (assignments_outside numbers column lower upper)

variable {F : Type} [Field F] [DecidableEq F]
def flags (base : Nat → F) (column : Nat) : Bool := decide (base column = 1)

theorem flags_cast (base : Nat → F) (column : Nat)
    (boolean : base column = 0 ∨ base column = 1) :
    (if flags base column then (1 : F) else 0) = base column := by
  rcases boolean with zero | one
  · simp only [flags,zero,zero_ne_one,decide_false,Bool.false_eq_true,if_false]
  · simp only [flags,one,decide_true,if_true]

theorem indicator_boolean (value : F) :
    CompilerZeroTest65.indicator value = 0 ∨ CompilerZeroTest65.indicator value = 1 := by
  classical
  by_cases zero : value = 0
  · right
    exact if_pos zero
  · left
    exact if_neg zero

theorem selected_frame (base : Nat → F) (numbers : Nat → Nat) (column : Nat)
    (lower : 113 ≤ column) (upper : column < 135)
    (selected : column ∈ SharedWordWitness221.seedColumns)
    (boolean : base column = 0 ∨ base column = 1) :
    SharedWordWitness221.seeded base numbers (flags base) column = base column := by
  unfold SharedWordWitness221.seeded
  rw [BooleanHints207.seeded_selected base _ _ column selected,
    bits_outside numbers (flags base) column lower upper]
  exact flags_cast base column boolean

theorem unselected_frame (base : Nat → F) (numbers : Nat → Nat) (column : Nat)
    (unselected : column ∉ SharedWordWitness221.seedColumns) :
    SharedWordWitness221.seeded base numbers (flags base) column = base column :=
  BooleanHints207.seeded_outside base _ _ column unselected

theorem hint_frame (base : Nat → F) (numbers : Nat → Nat) (column : Nat)
    (lower : 113 ≤ column) (upper : column < 135)
    (boolean_if_selected : column ∈ SharedWordWitness221.seedColumns →
      base column = 0 ∨ base column = 1) :
    SharedWordWitness221.seeded base numbers (flags base) column = base column := by
  by_cases selected : column ∈ SharedWordWitness221.seedColumns
  · exact selected_frame base numbers column lower upper selected (boolean_if_selected selected)
  · exact unselected_frame base numbers column selected
end ShielddSecurity.ZeroHintWordFrame303

