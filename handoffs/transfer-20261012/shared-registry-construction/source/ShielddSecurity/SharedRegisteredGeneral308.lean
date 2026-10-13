import ShielddSecurity.ZeroHintBooleanShape304
import ShielddSecurity.RegistrySeedFrame265
import ShielddSecurity.CapturedGlobalRegistered74
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedRegisteredGeneral308
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [DecidableEq F]

def prepared (base : Nat → F) : Nat → F := CapturedRegisteredHints72.seeded base
def seeded (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → F :=
  SharedWordWitness221.seeded (prepared base) numbers fallback
def completed (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) : Nat → F :=
  CapturedFullRelation58.candidate (seeded base numbers fallback)

def Matches (base : Nat → F) (fallback : Nat → Bool) : Prop :=
  ∀ column, column = 10 ∨ (113 ≤ column ∧ column < 135) →
    fallback column = ZeroHintWordFrame303.flags (prepared base) column

theorem hint_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (agrees : Matches base fallback) (column : Nat) (lower : 113 ≤ column) (upper : column < 135)
    (boolean : column ∈ SharedWordWitness221.seedColumns → prepared base column = 0 ∨ prepared base column = 1) :
    seeded base numbers fallback column = prepared base column := by
  by_cases selected : column ∈ SharedWordWitness221.seedColumns
  · unfold seeded SharedWordWitness221.seeded
    rw [BooleanHints207.seeded_selected _ _ _ column selected,
      ZeroHintWordFrame303.bits_outside numbers fallback column lower upper,
      agrees column (Or.inr ⟨lower,upper⟩)]
    exact ZeroHintWordFrame303.flags_cast _ column (boolean selected)
  · exact BooleanHints207.seeded_outside _ _ _ column selected

theorem indicator_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (agrees : Matches base fallback) (index : Nat) (bound : index < 10) :
    seeded base numbers fallback (115 + 2 * index) = prepared base (115 + 2 * index) := by
  apply hint_frame base numbers fallback agrees _ (by omega) (by omega)
  intro _
  change CapturedRegisteredHints72.seeded base (115 + 2 * index) = 0 ∨
    CapturedRegisteredHints72.seeded base (115 + 2 * index) = 1
  rw [(CapturedRegisteredHints72.seeded_values base index bound).1]
  exact ZeroHintWordFrame303.indicator_boolean _

theorem inverse_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (index : Nat) (bound : index < 10) :
    seeded base numbers fallback (116 + 2 * index) = prepared base (116 + 2 * index) := by
  apply BooleanHints207.seeded_outside
  intro selected
  have odd := ZeroHintBooleanShape304.selected_odd (116 + 2 * index) selected (by omega) (by omega)
  omega

theorem support_checked : (List.range 10).all (fun index =>
    (CapturedRegisteredAudit70.zeroTerms index).all (fun term =>
      decide (term.1 = 0 ∨ term.1 = 35 ∨ term.1 = 36 ∨ term.1 = 42 ∨ term.1 = 43))) = true := by decide +kernel

theorem support (index : Nat) (bound : index < 10) (column : Nat) (coefficient : Int)
    (member : (column,coefficient) ∈ CapturedRegisteredAudit70.zeroTerms index) :
    column = 0 ∨ column = 35 ∨ column = 36 ∨ column = 42 ∨ column = 43 :=
  of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp support_checked) index
    (List.mem_range.mpr bound))) (column,coefficient) member)

theorem term_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (index : Nat) (bound : index < 10) :
    eval (seeded base numbers fallback) (CapturedRegisteredAudit70.zeroTerms index) =
      eval (prepared base) (CapturedRegisteredAudit70.zeroTerms index) := by
  apply CapturedRegisteredHints72.eval_frame
  intro column coefficient member
  rcases support index bound column coefficient member with rfl | rfl | rfl | rfl | rfl
  · exact (SharedWordWitness221.seeded_fixed _ _ _).1
  all_goals exact RegistrySeedFrame265.seeded_frame _ _ _ _ (by constructor <;> omega)

theorem seeded_primitive (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (agrees : Matches base fallback) :
    CapturedRegisteredAudit70.Primitive (seeded base numbers fallback) := by
  intro index bound
  rw [term_frame base numbers fallback index bound, indicator_frame base numbers fallback agrees index bound,
    inverse_frame base numbers fallback index bound]
  exact CapturedRegisteredHints72.seeded_primitive base index bound

theorem candidate_original (base : Nat → F) (column : Nat)
    (lower : 3 ≤ column) (upper : column < 22738) :
    CapturedFullRelation58.candidate base column = base column := by
  have equal : 3 + (column - 3) = column := by omega
  have known := CapturedFullRelation58.candidate_inputs base (column - 3) (by omega)
  rw [equal] at known
  exact known

theorem completed_term_frame (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (index : Nat) (bound : index < 10) :
    eval (completed base numbers fallback) (CapturedRegisteredAudit70.zeroTerms index) =
      eval (seeded base numbers fallback) (CapturedRegisteredAudit70.zeroTerms index) := by
  apply CapturedRegisteredHints72.eval_frame
  intro column coefficient member
  rcases support index bound column coefficient member with rfl | rfl | rfl | rfl | rfl
  · exact CapturedFullRelation58.candidate_outside _ 0 (Or.inl (by decide)) (by constructor <;> decide)
  all_goals exact candidate_original _ _ (by decide) (by decide)

theorem completed_primitive (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (agrees : Matches base fallback) :
    CapturedRegisteredAudit70.Primitive (completed base numbers fallback) := by
  intro index bound
  rw [completed_term_frame base numbers fallback index bound]
  change CompilerZeroTest65.Primitive
    (eval (seeded base numbers fallback) (CapturedRegisteredAudit70.zeroTerms index))
    (CapturedFullRelation58.candidate (seeded base numbers fallback) (115 + 2 * index))
    (CapturedFullRelation58.candidate (seeded base numbers fallback) (116 + 2 * index))
  rw [candidate_original _ _ (by omega) (by omega), candidate_original _ _ (by omega) (by omega)]
  exact seeded_primitive base numbers fallback agrees index bound


theorem word_starts : CapturedWordRoot213.words.all (fun entry => decide (10 < entry.1.start)) = true := by decide +kernel

theorem outside_ten (numbers : Nat → Nat) :
    (10 : Nat) ∉ (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers).map Prod.fst := by
  intro member
  obtain ⟨pair, selected, same⟩ := List.mem_map.mp member
  obtain ⟨slot, known, paired⟩ := List.mem_flatMap.mp selected
  obtain ⟨entry, entryKnown, slotEqual⟩ := List.mem_map.mp known
  subst slot
  rcases pair with ⟨column, bit⟩
  have inside := (List.of_mem_zip paired).1
  have lower := of_decide_eq_true ((List.all_eq_true.mp word_starts) entry entryKnown)
  obtain ⟨offset, bound, equal⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at equal
  change column = 10 at same
  omega

theorem control_seeded (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (agrees : Matches base fallback) (boolean : base 10 = 0 ∨ base 10 = 1) :
    seeded base numbers fallback 10 = prepared base 10 := by
  change SharedWordWitness221.seeded (prepared base) numbers
    fallback 10 = prepared base 10
  by_cases selected : (10 : Nat) ∈ SharedWordWitness221.seedColumns
  · unfold SharedWordWitness221.seeded
    rw [BooleanHints207.seeded_selected _ _ _ 10 selected]
    have bits : SharedWordWitness221.bits numbers fallback 10 = fallback 10 :=
      SharedWordFlags220.chosen_outside _ _ 10 (outside_ten numbers)
    rw [bits, agrees 10 (Or.inl rfl)]
    apply ZeroHintWordFrame303.flags_cast
    change CapturedRegisteredHints72.seeded base 10 = 0 ∨ CapturedRegisteredHints72.seeded base 10 = 1
    rw [CapturedRegisteredHints72.seeded_outside base 10 (by omega)]
    exact boolean
  · exact BooleanHints207.seeded_outside _ _ _ 10 selected

theorem seeded_guards (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (agrees : Matches base fallback) (boolean : base 10 = 0 ∨ base 10 = 1) (legal : CapturedRegisteredHints72.LegalGuards base) :
    CapturedRegisteredAudit71.Guards (seeded base numbers fallback) := by
  intro pair bound
  have a := indicator_frame base numbers fallback agrees (2 * pair) (by omega)
  have b := indicator_frame base numbers fallback agrees (2 * pair + 1) (by omega)
  have left : 115 + 2 * (2 * pair) = 115 + 4 * pair := by omega
  have right : 115 + 2 * (2 * pair + 1) = 117 + 4 * pair := by omega
  rw [left] at a
  rw [right] at b
  rw [control_seeded base numbers fallback agrees boolean, a, b]
  exact CapturedRegisteredHints72.seeded_guards base legal pair bound

theorem completed_guards (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (agrees : Matches base fallback) (boolean : base 10 = 0 ∨ base 10 = 1) (legal : CapturedRegisteredHints72.LegalGuards base) :
    CapturedRegisteredAudit71.Guards (completed base numbers fallback) := by
  intro pair bound
  change CapturedFullRelation58.candidate (seeded base numbers fallback) 10 *
    (CapturedFullRelation58.candidate (seeded base numbers fallback) (115 + 4 * pair) *
      CapturedFullRelation58.candidate (seeded base numbers fallback) (117 + 4 * pair)) = 0
  rw [candidate_original _ 10 (by decide) (by decide),
    candidate_original _ (115 + 4 * pair) (by omega) (by omega),
    candidate_original _ (117 + 4 * pair) (by omega) (by omega)]
  exact seeded_guards base numbers fallback agrees boolean legal pair bound

variable [CharP F p]
theorem completed_zero (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0 = 1) :
    completed base numbers fallback 0 = 1 := by
  exact (CapturedFullRelation58.candidate_outside _ 0 (Or.inl (by decide)) (by constructor <;> decide)).trans
    ((SharedWordWitness221.seeded_fixed _ _ _).1.trans
      ((CapturedRegisteredHints72.seeded_outside base 0 (by omega)).trans one))

theorem completed_arithmetic (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    Satisfies (completed base numbers fallback) CapturedRegisteredAudit70.arithmetic :=
  CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 262 60
    CapturedRegisteredAudit70.arithmetic (Bool.and_eq_true_iff.mp CapturedGlobalRegistered74.arithmetic_checked).2
    (by decide) (completed base numbers fallback) (CapturedFullRelation58.candidate_arithmetic _)

theorem completed_assertions (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0 = 1)
    (agrees : Matches base fallback) (boolean : base 10 = 0 ∨ base 10 = 1) (legal : CapturedRegisteredHints72.LegalGuards base) :
    CompilerAssertionBlock51.SatisfiesAt (completed base numbers fallback) CapturedRegisteredAudit70.block.actual 35 :=
  CapturedRegisteredAssertions73.primitive_assertions (completed base numbers fallback)
    (completed_zero base numbers fallback one) (CapturedFullRelation58.candidate_links _).2.2
    (completed_arithmetic base numbers fallback) (completed_primitive base numbers fallback agrees)
    (completed_guards base numbers fallback agrees boolean legal)
end ShielddSecurity.SharedRegisteredGeneral308

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.prepared
#print axioms ShielddSecurity.SharedRegisteredGeneral308.prepared

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.seeded
#print axioms ShielddSecurity.SharedRegisteredGeneral308.seeded

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.Matches
#print axioms ShielddSecurity.SharedRegisteredGeneral308.Matches

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.hint_frame
#print axioms ShielddSecurity.SharedRegisteredGeneral308.hint_frame

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.indicator_frame
#print axioms ShielddSecurity.SharedRegisteredGeneral308.indicator_frame

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.inverse_frame
#print axioms ShielddSecurity.SharedRegisteredGeneral308.inverse_frame

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.support_checked
#print axioms ShielddSecurity.SharedRegisteredGeneral308.support_checked

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.support
#print axioms ShielddSecurity.SharedRegisteredGeneral308.support

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.term_frame
#print axioms ShielddSecurity.SharedRegisteredGeneral308.term_frame

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.seeded_primitive
#print axioms ShielddSecurity.SharedRegisteredGeneral308.seeded_primitive

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.candidate_original
#print axioms ShielddSecurity.SharedRegisteredGeneral308.candidate_original

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed_term_frame
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed_term_frame

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed_primitive
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed_primitive

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.word_starts
#print axioms ShielddSecurity.SharedRegisteredGeneral308.word_starts

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.outside_ten
#print axioms ShielddSecurity.SharedRegisteredGeneral308.outside_ten

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.control_seeded
#print axioms ShielddSecurity.SharedRegisteredGeneral308.control_seeded

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.seeded_guards
#print axioms ShielddSecurity.SharedRegisteredGeneral308.seeded_guards

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed_guards
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed_guards

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed_zero
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed_zero

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed_arithmetic
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed_arithmetic

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredGeneral308.completed_assertions
#print axioms ShielddSecurity.SharedRegisteredGeneral308.completed_assertions
