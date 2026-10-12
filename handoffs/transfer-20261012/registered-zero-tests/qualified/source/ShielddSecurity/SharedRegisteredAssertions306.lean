import ShielddSecurity.SharedZeroPrimitives305
import ShielddSecurity.CapturedGlobalRegistered74
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedRegisteredAssertions306
open Compiler CompilerArithmeticTransport41 SharedZeroPrimitives305 WordHints210
variable {F : Type} [Field F] [DecidableEq F]

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

theorem control_seeded (base : Nat → F) (numbers : Nat → Nat) (boolean : base 10 = 0 ∨ base 10 = 1) :
    seeded base numbers 10 = prepared base 10 := by
  change SharedWordWitness221.seeded (prepared base) numbers
    (ZeroHintWordFrame303.flags (prepared base)) 10 = prepared base 10
  by_cases selected : (10 : Nat) ∈ SharedWordWitness221.seedColumns
  · unfold SharedWordWitness221.seeded
    rw [BooleanHints207.seeded_selected _ _ _ 10 selected]
    have bits : SharedWordWitness221.bits numbers (ZeroHintWordFrame303.flags (prepared base)) 10 =
        ZeroHintWordFrame303.flags (prepared base) 10 :=
      SharedWordFlags220.chosen_outside _ _ 10 (outside_ten numbers)
    rw [bits]
    apply ZeroHintWordFrame303.flags_cast
    change CapturedRegisteredHints72.seeded base 10 = 0 ∨ CapturedRegisteredHints72.seeded base 10 = 1
    rw [CapturedRegisteredHints72.seeded_outside base 10 (by omega)]
    exact boolean
  · exact BooleanHints207.seeded_outside _ _ _ 10 selected

theorem seeded_guards (base : Nat → F) (numbers : Nat → Nat)
    (boolean : base 10 = 0 ∨ base 10 = 1) (legal : CapturedRegisteredHints72.LegalGuards base) :
    CapturedRegisteredAudit71.Guards (seeded base numbers) := by
  intro pair bound
  have a := indicator_frame base numbers (2 * pair) (by omega)
  have b := indicator_frame base numbers (2 * pair + 1) (by omega)
  have left : 115 + 2 * (2 * pair) = 115 + 4 * pair := by omega
  have right : 115 + 2 * (2 * pair + 1) = 117 + 4 * pair := by omega
  rw [left] at a
  rw [right] at b
  rw [control_seeded base numbers boolean, a, b]
  exact CapturedRegisteredHints72.seeded_guards base legal pair bound

theorem completed_guards (base : Nat → F) (numbers : Nat → Nat)
    (boolean : base 10 = 0 ∨ base 10 = 1) (legal : CapturedRegisteredHints72.LegalGuards base) :
    CapturedRegisteredAudit71.Guards (completed base numbers) := by
  intro pair bound
  change CapturedFullRelation58.candidate (seeded base numbers) 10 *
    (CapturedFullRelation58.candidate (seeded base numbers) (115 + 4 * pair) *
      CapturedFullRelation58.candidate (seeded base numbers) (117 + 4 * pair)) = 0
  rw [candidate_original _ 10 (by decide) (by decide),
    candidate_original _ (115 + 4 * pair) (by omega) (by omega),
    candidate_original _ (117 + 4 * pair) (by omega) (by omega)]
  exact seeded_guards base numbers boolean legal pair bound

variable [CharP F p]
theorem completed_zero (base : Nat → F) (numbers : Nat → Nat) (one : base 0 = 1) :
    completed base numbers 0 = 1 := by
  exact (CapturedFullRelation58.candidate_outside _ 0 (Or.inl (by decide)) (by constructor <;> decide)).trans
    ((SharedWordWitness221.seeded_fixed _ _ _).1.trans
      ((CapturedRegisteredHints72.seeded_outside base 0 (by omega)).trans one))

theorem completed_arithmetic (base : Nat → F) (numbers : Nat → Nat) :
    Satisfies (completed base numbers) CapturedRegisteredAudit70.arithmetic :=
  CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 262 60
    CapturedRegisteredAudit70.arithmetic (Bool.and_eq_true_iff.mp CapturedGlobalRegistered74.arithmetic_checked).2
    (by decide) (completed base numbers) (CapturedFullRelation58.candidate_arithmetic _)

theorem completed_assertions (base : Nat → F) (numbers : Nat → Nat) (one : base 0 = 1)
    (boolean : base 10 = 0 ∨ base 10 = 1) (legal : CapturedRegisteredHints72.LegalGuards base) :
    CompilerAssertionBlock51.SatisfiesAt (completed base numbers) CapturedRegisteredAudit70.block.actual 35 :=
  CapturedRegisteredAssertions73.primitive_assertions (completed base numbers)
    (completed_zero base numbers one) (CapturedFullRelation58.candidate_links _).2.2
    (completed_arithmetic base numbers) (completed_primitive base numbers)
    (completed_guards base numbers boolean legal)
end ShielddSecurity.SharedRegisteredAssertions306


set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.word_starts
#print axioms ShielddSecurity.SharedRegisteredAssertions306.word_starts

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.outside_ten
#print axioms ShielddSecurity.SharedRegisteredAssertions306.outside_ten

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.control_seeded
#print axioms ShielddSecurity.SharedRegisteredAssertions306.control_seeded

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.seeded_guards
#print axioms ShielddSecurity.SharedRegisteredAssertions306.seeded_guards

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.completed_guards
#print axioms ShielddSecurity.SharedRegisteredAssertions306.completed_guards

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.completed_zero
#print axioms ShielddSecurity.SharedRegisteredAssertions306.completed_zero

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.completed_arithmetic
#print axioms ShielddSecurity.SharedRegisteredAssertions306.completed_arithmetic

set_option pp.all true in
#check @ShielddSecurity.SharedRegisteredAssertions306.completed_assertions
#print axioms ShielddSecurity.SharedRegisteredAssertions306.completed_assertions
