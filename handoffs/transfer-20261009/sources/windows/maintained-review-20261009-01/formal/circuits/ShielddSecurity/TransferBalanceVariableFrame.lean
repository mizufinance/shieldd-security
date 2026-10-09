import ShielddSecurity.RuntimeBalanceVariableSequence
import ShielddSecurity.GroupCircuitFrameTrace
import ShielddSecurity.RuntimeBalanceBlindingTemplateFrameBounds

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceVariableFrame

open GroupFixedCircuitBounds

private theorem checked_rows (frame : Frame) (rows : List Row)
    (checked : rows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (covers 22738 200692 frame term.1))) = true) :
    RowsCovered 22738 200692 frame rows := by
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)

theorem initial_covered : RowsCovered 22738 200692
    RuntimeBalanceVariableWindow000Program.beforeFrame
    RuntimeBalanceVariableSequence.priorRows :=
  checked_rows _ _ (by decide)

theorem variable_covered (n : Nat) : RowsCovered 22738 200692
    RuntimeBalanceBlindingTemplateFrameBounds.before
    (RuntimeBalanceVariableSequence.ownedRows n) := by
  have covered := GroupCircuitFrameTrace.rows_covered_final 22738 200692
    RuntimeBalanceVariableWindow000Program.beforeFrame
    RuntimeBalanceVariableSequence.priorRows
    (RuntimeBalanceVariableSequence.segments n) initial_covered
    (RuntimeBalanceVariableSequence.certified_bounds n)
  have finalFrame : GroupCircuitFrameTrace.lastFrame
      RuntimeBalanceVariableWindow000Program.beforeFrame
      (RuntimeBalanceVariableSequence.segments n) =
      RuntimeBalanceBlindingTemplateFrameBounds.before := rfl
  have programs : (RuntimeBalanceVariableSequence.segments n).map Prod.fst =
      RuntimeBalanceVariableSequence.programs n := rfl
  rw [finalFrame, programs] at covered
  exact covered

theorem signed_covered : RowsCovered 22738 200692
    RuntimeBalanceBlindingTemplateFrameBounds.before
    RuntimeTransferSignedBalanceCompletion.rawRows :=
  checked_rows _ _ (by decide)

/-- H construction preserves the actual signed and variable relation, using
the proved support fence rather than any claimed output semantics. -/
theorem h_preserves {F : Type} [Field F] (rho : Nat → F) (n b : Nat)
    (initial : Satisfies rho (RuntimeTransferSignedBalanceCompletion.rawRows ++
      RuntimeBalanceVariableSequence.ownedRows n)) :
    Satisfies (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho b)
      (RuntimeTransferSignedBalanceCompletion.rawRows ++
        RuntimeBalanceVariableSequence.ownedRows n) := by
  apply RuntimeBalanceBlindingTemplateFrameBounds.preserves_prior rho b _ _ initial
  intro row member term present
  rcases List.mem_append.mp member with signed | windowRows
  · exact signed_covered row signed term present
  · exact variable_covered n row windowRows term present

set_option pp.all true in
#check @initial_covered
#print axioms initial_covered
set_option pp.all true in
#check @variable_covered
#print axioms variable_covered
set_option pp.all true in
#check @signed_covered
#print axioms signed_covered
set_option pp.all true in
#check @h_preserves
#print axioms h_preserves
end ShielddSecurity.TransferBalanceVariableFrame
