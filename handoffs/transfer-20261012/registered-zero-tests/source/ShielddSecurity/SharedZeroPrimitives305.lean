import ShielddSecurity.ZeroHintBooleanShape304
import ShielddSecurity.RegistrySeedFrame265
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedZeroPrimitives305
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [DecidableEq F]

def prepared (base : Nat → F) : Nat → F := CapturedRegisteredHints72.seeded base
def seeded (base : Nat → F) (numbers : Nat → Nat) : Nat → F :=
  SharedWordWitness221.seeded (prepared base) numbers (ZeroHintWordFrame303.flags (prepared base))
def completed (base : Nat → F) (numbers : Nat → Nat) : Nat → F :=
  CapturedFullRelation58.candidate (seeded base numbers)

theorem indicator_frame (base : Nat → F) (numbers : Nat → Nat) (index : Nat) (bound : index < 10) :
    seeded base numbers (115 + 2 * index) = prepared base (115 + 2 * index) := by
  apply ZeroHintWordFrame303.hint_frame _ numbers _ (by omega) (by omega)
  intro _
  change CapturedRegisteredHints72.seeded base (115 + 2 * index) = 0 ∨
    CapturedRegisteredHints72.seeded base (115 + 2 * index) = 1
  rw [(CapturedRegisteredHints72.seeded_values base index bound).1]
  exact ZeroHintWordFrame303.indicator_boolean _

theorem inverse_frame (base : Nat → F) (numbers : Nat → Nat) (index : Nat) (bound : index < 10) :
    seeded base numbers (116 + 2 * index) = prepared base (116 + 2 * index) := by
  apply ZeroHintWordFrame303.unselected_frame
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

theorem term_frame (base : Nat → F) (numbers : Nat → Nat) (index : Nat) (bound : index < 10) :
    eval (seeded base numbers) (CapturedRegisteredAudit70.zeroTerms index) =
      eval (prepared base) (CapturedRegisteredAudit70.zeroTerms index) := by
  apply CapturedRegisteredHints72.eval_frame
  intro column coefficient member
  rcases support index bound column coefficient member with rfl | rfl | rfl | rfl | rfl
  · exact (SharedWordWitness221.seeded_fixed _ _ _).1
  all_goals exact RegistrySeedFrame265.seeded_frame _ _ _ _ (by constructor <;> omega)

theorem seeded_primitive (base : Nat → F) (numbers : Nat → Nat) :
    CapturedRegisteredAudit70.Primitive (seeded base numbers) := by
  intro index bound
  rw [term_frame base numbers index bound, indicator_frame base numbers index bound,
    inverse_frame base numbers index bound]
  exact CapturedRegisteredHints72.seeded_primitive base index bound

theorem candidate_original (base : Nat → F) (column : Nat)
    (lower : 3 ≤ column) (upper : column < 22738) :
    CapturedFullRelation58.candidate base column = base column := by
  have equal : 3 + (column - 3) = column := by omega
  have known := CapturedFullRelation58.candidate_inputs base (column - 3) (by omega)
  rw [equal] at known
  exact known

theorem completed_term_frame (base : Nat → F) (numbers : Nat → Nat) (index : Nat) (bound : index < 10) :
    eval (completed base numbers) (CapturedRegisteredAudit70.zeroTerms index) =
      eval (seeded base numbers) (CapturedRegisteredAudit70.zeroTerms index) := by
  apply CapturedRegisteredHints72.eval_frame
  intro column coefficient member
  rcases support index bound column coefficient member with rfl | rfl | rfl | rfl | rfl
  · exact CapturedFullRelation58.candidate_outside _ 0 (Or.inl (by decide)) (by constructor <;> decide)
  all_goals exact candidate_original _ _ (by decide) (by decide)

theorem completed_primitive (base : Nat → F) (numbers : Nat → Nat) :
    CapturedRegisteredAudit70.Primitive (completed base numbers) := by
  intro index bound
  rw [completed_term_frame base numbers index bound]
  change CompilerZeroTest65.Primitive
    (eval (seeded base numbers) (CapturedRegisteredAudit70.zeroTerms index))
    (CapturedFullRelation58.candidate (seeded base numbers) (115 + 2 * index))
    (CapturedFullRelation58.candidate (seeded base numbers) (116 + 2 * index))
  rw [candidate_original _ _ (by omega) (by omega), candidate_original _ _ (by omega) (by omega)]
  exact seeded_primitive base numbers index bound
end ShielddSecurity.SharedZeroPrimitives305

