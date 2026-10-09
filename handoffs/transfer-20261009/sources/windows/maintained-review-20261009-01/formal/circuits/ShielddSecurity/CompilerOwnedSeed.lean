import ShielddSecurity.GroupCircuitSupportPreservation

set_option maxHeartbeats 100000

namespace ShielddSecurity.CompilerOwnedSeed

variable {F : Type} [Field F]

/-- Initial native input assignment is idempotent. Values and columns are
fixed by the input reader; they do not depend on the assignment being patched. -/
theorem patch_idempotent (base values : Nat → F) (columns : List Nat) :
    patchAssignment (patchAssignment base values columns) values columns =
      patchAssignment base values columns := by
  funext column
  by_cases member : column ∈ columns <;> simp [patchAssignment,member]

/-- Reseeding after earlier constructors changes nothing when their actual
write-exclusion proofs establish preservation of the seeded input columns. -/
theorem reseed_of_columns (base values completed : Nat → F) (columns : List Nat)
    (preserved : ∀ column ∈ columns,
      completed column = patchAssignment base values columns column) :
    patchAssignment completed values columns = completed := by
  funext column
  by_cases member : column ∈ columns
  · have same := preserved column member
    simp only [patchAssignment,if_pos member] at same ⊢
    exact same.symm
  · exact patchAssignment_preserves completed values columns column member

/-- The preservation premise above follows symbolically from reviewed actual
stage writes. This lemma has no constraint satisfaction or endpoint premise. -/
theorem mixed_run_reseed (base values : Nat → F) (columns : List Nat)
    (stages : List GroupCircuitCompletion.Step)
    (outside : ∀ column ∈ columns, ∀ stage ∈ stages, column ∉ stage.writes) :
    patchAssignment (GroupCircuitCompletion.run (patchAssignment base values columns) stages)
      values columns = GroupCircuitCompletion.run (patchAssignment base values columns) stages := by
  apply reseed_of_columns base values
  intro column member
  exact GroupCircuitSupportPreservation.run_outside _ stages column (outside column member)

set_option pp.all true in
#check @patch_idempotent
#print axioms patch_idempotent
set_option pp.all true in
#check @reseed_of_columns
#print axioms reseed_of_columns
set_option pp.all true in
#check @mixed_run_reseed
#print axioms mixed_run_reseed

end ShielddSecurity.CompilerOwnedSeed
