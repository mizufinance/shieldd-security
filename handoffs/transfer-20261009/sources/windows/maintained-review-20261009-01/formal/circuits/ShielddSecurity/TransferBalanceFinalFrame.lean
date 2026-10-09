import ShielddSecurity.TransferBalanceVariableFrame
import ShielddSecurity.TransferBalanceBlindingCommittedRelation
import ShielddSecurity.RuntimeTransferBalanceFinalAddCompletion

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferBalanceFinalFrame

open GroupFixedCircuitBounds

def before : Frame := ⟨22736,195214⟩
def exceptions : List Nat := [192706,192707]
def priorRows (n : Nat) : List Row := RuntimeTransferSignedBalanceCompletion.rawRows ++
  (RuntimeBalanceVariableSequence.ownedRows n ++ TransferBalanceBlindingCommittedRelation.rows)

private theorem checked_rows (origin : Nat) (frame : Frame) (rows : List Row)
    (checked : rows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (covers origin 200692 frame term.1))) = true) :
    RowsCovered origin 200692 frame rows := by
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)

theorem h_rows_covered : RowsCovered 192708 200692 before
    TransferBalanceBlindingCommittedRelation.rows := by
  let initialRows := TransferBalanceBlindingCommittedRelation.inputRows ++
    (RuntimeBalanceBlindingCanonical.originalRows ++ RuntimeBalanceBlindingWindow000.rawRows)
  have initial : RowsCovered 192708 200692
      RuntimeBalanceBlindingWindow001TemplateTrace.before initialRows :=
    checked_rows _ _ _ (by decide)
  have covered := GroupCircuitFrameTrace.rows_covered_final 192708 200692
    RuntimeBalanceBlindingWindow001TemplateTrace.before initialRows
    (RuntimeBalanceBlindingTemplateOrdinaryTrace.segments 0) initial
    (RuntimeBalanceBlindingTemplateOrdinaryTrace.certified_bounds 0)
  have finalFrame : GroupCircuitFrameTrace.lastFrame
      RuntimeBalanceBlindingWindow001TemplateTrace.before
      (RuntimeBalanceBlindingTemplateOrdinaryTrace.segments 0) = before := rfl
  rw [finalFrame, RuntimeBalanceBlindingTemplateOrdinaryTrace.segments_programs] at covered
  simpa only [initialRows, TransferBalanceBlindingCommittedRelation.rows,
    TransferBalanceBlindingCanonicalFixedRelation.rows,
    RuntimeBalanceBlindingTemplateScalarSoundness.rows, List.append_assoc] using covered

private theorem prior_column (n : Nat) (row : Row) (member : row ∈ priorRows n)
    (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    covers 22738 200692 before term.1 ∧ term.1 ∉ exceptions := by
  have previous : covers 22738 200692
      RuntimeBalanceBlindingTemplateFrameBounds.before term.1 ∨
      covers 192708 200692 before term.1 := by
    rcases List.mem_append.mp member with signed | remaining
    · exact Or.inl (TransferBalanceVariableFrame.signed_covered row signed term present)
    · rcases List.mem_append.mp remaining with windowRows | blinding
      · exact Or.inl (TransferBalanceVariableFrame.variable_covered n row windowRows term present)
      · exact Or.inr (h_rows_covered row blinding term present)
  change (term.1 < 22232 ∨ (22738 ≤ term.1 ∧ term.1 < 192706) ∨ term.1 = 200692) ∨
    (term.1 < 22736 ∨ (192708 ≤ term.1 ∧ term.1 < 195214) ∨ term.1 = 200692) at previous
  have boundary : covers 22738 200692 before term.1 ∧
      term.1 ≠ 192706 ∧ term.1 ≠ 192707 := by
    change (term.1 < 22736 ∨ (22738 ≤ term.1 ∧ term.1 < 195214) ∨ term.1 = 200692) ∧
      term.1 ≠ 192706 ∧ term.1 ≠ 192707
    rcases previous with (low | high | copied) | (low | high | copied) <;> omega
  refine ⟨boundary.1, ?_⟩
  simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact boundary.2

theorem writes_checked : RuntimeTransferBalanceFinalAddCompletion.ownedWrites.all
    (fun column => decide (¬ covers 22738 200692 before column ∨ column ∈ exceptions)) = true :=
  by decide

theorem prior_outside (n : Nat) : ∀ row ∈ priorRows n, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ RuntimeTransferBalanceFinalAddCompletion.ownedWrites := by
  intro row member term present written
  have boundary := prior_column n row member term present
  have alternative := of_decide_eq_true
    (List.all_eq_true.mp writes_checked term.1 written)
  rcases alternative with outside | exceptional
  · exact outside boundary.1
  · exact boundary.2 exceptional

/-- The two early final-add product allocations are actual source exceptions.
Their exclusion is derived from symbolic row support for both preceding loops. -/
theorem preserves_prior {F : Type} [Field F] (rho : Nat → F) (n : Nat)
    (initial : Satisfies rho (priorRows n)) :
    Satisfies (RuntimeTransferBalanceFinalAddCompletion.completeAssignment rho) (priorRows n) := by
  intro row member
  have agree : ∀ terms : Linear, (∀ term ∈ terms,
      term.1 ∉ RuntimeTransferBalanceFinalAddCompletion.ownedWrites) →
      eval (RuntimeTransferBalanceFinalAddCompletion.completeAssignment rho) terms = eval rho terms := by
    intro terms absent
    apply eval_agrees
    intro term present
    exact RuntimeTransferBalanceFinalAddCompletion.outside rho term.1 (absent term present)
  change Square (eval _ row.a) (eval _ row.b)
  have leftOutside : ∀ term ∈ row.a,
      term.1 ∉ RuntimeTransferBalanceFinalAddCompletion.ownedWrites := by
    intro term present
    exact prior_outside n row member term (List.mem_append_left _ present)
  have rightOutside : ∀ term ∈ row.b,
      term.1 ∉ RuntimeTransferBalanceFinalAddCompletion.ownedWrites := by
    intro term present
    exact prior_outside n row member term (List.mem_append_right _ present)
  rw [agree row.a leftOutside, agree row.b rightOutside]
  exact initial row member

set_option pp.all true in
#check @h_rows_covered
#print axioms h_rows_covered
set_option pp.all true in
#check @writes_checked
#print axioms writes_checked
set_option pp.all true in
#check @prior_outside
#print axioms prior_outside
set_option pp.all true in
#check @preserves_prior
#print axioms preserves_prior
end ShielddSecurity.TransferBalanceFinalFrame
