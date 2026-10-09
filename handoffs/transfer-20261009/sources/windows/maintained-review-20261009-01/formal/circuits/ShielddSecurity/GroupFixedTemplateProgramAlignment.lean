import ShielddSecurity.GroupFixedTemplateTrace

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.GroupFixedTemplateProgramAlignment

open GroupFixedTemplateTrace

/-- Checked source input/output LCs transport table-trace adjacency to the
actual constructor programs. This is symbolic in the window count. -/
theorem checked_alignment (p copy : Nat) (d : Int) (windows : List Window)
    (input : Linear × Linear) (base : Group.Point Int)
    (aligned : Aligned input base windows)
    (checked : ∀ window ∈ windows, window.Checked p copy d) :
    GroupFixedCircuitCompletion.Aligned input (windows.map Window.program) := by
  induction windows generalizing input base with
  | nil => trivial
  | cons window tail ih =>
      have first := checked window (by simp)
      change window.program.input = input ∧
        GroupFixedCircuitCompletion.Aligned window.program.output (tail.map Window.program)
      refine ⟨first.1.trans aligned.1, ?_⟩
      rw [first.2.1]
      exact ih window.output window.nextBase aligned.2.2
        (by intro next present; exact checked next (List.mem_cons_of_mem _ present))

/-- The endpoint names the same actual quotient columns in both views. -/
theorem checked_output (p copy : Nat) (d : Int) (windows : List Window)
    (input : Linear × Linear)
    (checked : ∀ window ∈ windows, window.Checked p copy d) :
    GroupFixedCircuitCompletion.output input (windows.map Window.program) =
      endpoint input windows := by
  induction windows generalizing input with
  | nil => rfl
  | cons window tail ih =>
      have first := checked window (by simp)
      change GroupFixedCircuitCompletion.output window.program.output
        (tail.map Window.program) = endpoint window.output tail
      rw [first.2.1]
      exact ih window.output
        (by intro next present; exact checked next (List.mem_cons_of_mem _ present))

set_option pp.all true in
#check @checked_alignment
#print axioms checked_alignment
set_option pp.all true in
#check @checked_output
#print axioms checked_output

end ShielddSecurity.GroupFixedTemplateProgramAlignment
