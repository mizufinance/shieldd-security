import ShielddSecurity.TransferEpkScope1Completion

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferEpkScope1Frame

variable {F : Type} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

def Protected (column : Nat) : Prop :=
  RuntimeTransferEpk1RenamingMap.columns column ∈ RuntimeTransferEpk0CanonicalOrder.kept ∧
  RuntimeTransferEpk1RenamingMap.columns column ∈ RuntimeTransferEpk0FixedWindow000TemplatePrefix.kept ∧
  RuntimeTransferEpk1RenamingMap.columns column ∈ RuntimeTransferEpk0FixedTemplateOrdinaryTrace.kept ∧
  column ∉ RuntimeTransferEpk1CapturedPublication.writes

theorem preserves (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 6334 = (n : F)) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (column : Nat) (protection : Protected column) :
    TransferEpkScope1Completion.construct rho n column = rho column := by
  rw [TransferEpkScope1Completion.construct,
    RuntimeTransferEpk1CapturedPublication.preserves _ column protection.2.2.2]
  have group := TransferEpkScope1Completion.group_preserves rho n canonical meaning one four
    (RuntimeTransferEpk1RenamingMap.columns column) protection.1 protection.2.1 protection.2.2.1
  simpa only [RuntimeTransferEpk1RenamingMap.inverted] using group

theorem prior_rows (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 6334 = (n : F)) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row)
    (support : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,Protected term.1)
    (satisfied : Satisfies rho rows) :
    Satisfies (TransferEpkScope1Completion.construct rho n) rows := by
  intro row member
  have agree (terms : Linear) (included : ∀ term ∈ terms,term ∈ row.a ++ row.b) :
      eval (TransferEpkScope1Completion.construct rho n) terms = eval rho terms := by
    apply eval_agrees
    intro term present
    exact preserves rho n canonical meaning one four term.1
      (support row member term (included term present))
  rw [agree row.a (by intro term present;exact List.mem_append_left _ present),
    agree row.b (by intro term present;exact List.mem_append_right _ present)]
  exact satisfied row member

set_option pp.all true in
#check @preserves
#print axioms preserves
set_option pp.all true in
#check @prior_rows
#print axioms prior_rows

end ShielddSecurity.TransferEpkScope1Frame
