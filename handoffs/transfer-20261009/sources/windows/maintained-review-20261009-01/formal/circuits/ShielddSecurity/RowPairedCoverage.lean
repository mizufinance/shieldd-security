import ShielddSecurity.Rows

set_option maxHeartbeats 100000

namespace ShielddSecurity.RowPairedCoverage

/-- Check a supplied pairing once, rather than search every source for each target. -/
def check {α β : Type} (relation : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | source :: sources, target :: targets =>
      relation source target && check relation sources targets
  | _, _ => false

/-- Every target has a checked source in the supplied paired list. -/
theorem covered {α β : Type} (relation : α → β → Bool)
    (sources : List α) (targets : List β)
    (checked : check relation sources targets = true) :
    ∀ target ∈ targets, ∃ source ∈ sources, relation source target = true := by
  induction sources generalizing targets with
  | nil =>
      cases targets with
      | nil => simp
      | cons target targets => simp [check] at checked
  | cons source sources induction =>
      cases targets with
      | nil => simp
      | cons target targets =>
          have facts : relation source target = true ∧
              check relation sources targets = true := by
            simpa only [check, Bool.and_eq_true] using checked
          intro wanted member
          rcases List.mem_cons.mp member with same | remaining
          · subst wanted
            exact ⟨source, List.mem_cons.mpr (Or.inl rfl), facts.1⟩
          · obtain ⟨witness, present, related⟩ := induction targets facts.2 wanted remaining
            exact ⟨witness, List.mem_cons.mpr (Or.inr present), related⟩

set_option pp.all true in
#check @covered
#print axioms covered

end ShielddSecurity.RowPairedCoverage
