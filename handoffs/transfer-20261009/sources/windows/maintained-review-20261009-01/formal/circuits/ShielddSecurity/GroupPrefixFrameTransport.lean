import ShielddSecurity.CompilerFrameCoverage
import ShielddSecurity.PoseidonCompletion
import ShielddSecurity.GroupCircuitSupportPreservation

set_option maxHeartbeats 200000

namespace ShielddSecurity.GroupPrefixFrameTransport

open GroupFixedCircuitBounds GroupFixedCircuitCompletion
variable {F : Type} [Field F]

private theorem lower_origin_writes (earlier later copy : Nat) (frame : Frame)
    (program : Program) (outside : WritesOutside later copy frame program)
    (gap : ∀ stage ∈ program.stages, ∀ column ∈ stage.writes,
      column < earlier ∨ later ≤ column) : WritesOutside earlier copy frame program := by
  intro stage member column written covered
  rcases covered with low | high | copied
  · exact outside stage member column written (Or.inl low)
  · rcases gap stage member column written with small | large
    · exact (Nat.not_lt_of_ge high.1) small
    · exact outside stage member column written (Or.inr (Or.inl ⟨large,high.2⟩))
  · exact outside stage member column written (Or.inr (Or.inr copied))

/-- Broaden already checked window allocation frames only after independent
actual write lists exclude the newly protected interval. This uses no physical
compiler allocation interpretation or row satisfaction premise. -/
theorem lower_origin_certified (earlier later copy : Nat) (before : Frame)
    (segments : List (Program × Frame)) (order : earlier ≤ later)
    (certificate : Certified later copy before segments)
    (gap : ∀ segment ∈ segments, ∀ stage ∈ segment.1.stages, ∀ column ∈ stage.writes,
      column < earlier ∨ later ≤ column) : Certified earlier copy before segments := by
  induction segments generalizing before with
  | nil => trivial
  | cons segment tail ih =>
      rcases segment with ⟨program,after⟩
      rcases certificate with ⟨growth,rows,outside,remaining⟩
      refine ⟨growth,CompilerFrameCoverage.lower_origin_rows earlier later copy after program.rows order rows,
        lower_origin_writes earlier later copy before program outside (gap _ (List.mem_cons_self)),?_⟩
      exact ih after remaining (by intro next member; exact gap next (List.mem_cons_of_mem _ member))

/-- Every original row support is preserved through the full symbolic window
sequence. Freshness is obtained from actual bounded frame/write certificates. -/
theorem fixed_run_support (base : Nat → F) (programs : List Program) (prior : List Row)
    (fresh : Fresh prior programs) (row : Row) (member : row ∈ prior)
    (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    GroupFixedCircuitCompletion.run base programs term.1 = base term.1 := by
  induction programs generalizing base prior with
  | nil => rfl
  | cons program tail ih =>
      exact (ih (program.build base) (prior ++ program.rows) fresh.2
        (List.mem_append_left program.rows member)).trans
        (GroupCircuitSupportPreservation.run_outside base program.stages term.1
          (fresh.1 row member term present))

theorem fixed_preserves_constructed_rows (base : Nat → F) (programs : List Program)
    (prior : List Row) (fresh : Fresh prior programs) (constructed : Satisfies base prior) :
    Satisfies (GroupFixedCircuitCompletion.run base programs) prior := by
  intro row member
  have preserved (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (GroupFixedCircuitCompletion.run base programs) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact fixed_run_support base programs prior fresh row member term (inside term present)
  rw [preserved row.a (by intro term present; exact List.mem_append_left row.b present),
    preserved row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact constructed row member

/-- The randomizer's fresh252-bit patch precedes the comparator products.
Actual earlier-row coverage independently excludes this bit interval. -/
theorem bit_patch_preserves_constructed_rows (base : Nat → F) (start : Nat) (bits : List Bool)
    (prior : List Row)
    (outside : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
      term.1 < start ∨ start + bits.length ≤ term.1)
    (constructed : Satisfies base prior) : Satisfies (writeBits base start bits) prior := by
  intro row member
  have preserved (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (writeBits base start bits) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact writeBits_preserves base start bits term.1 (outside row member term (inside term present))
  rw [preserved row.a (by intro term present; exact List.mem_append_left row.b present),
    preserved row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact constructed row member

/-- Comparator product construction preserves every previously constructed
original row, using its exact actual support and finite owned write lists. -/
theorem compiler_preserves_constructed_rows (base : Nat → F) (stages : List CompilerCompletion.Step)
    (prior : List Row)
    (outside : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
      term.1 ∉ PoseidonCompletion.writes stages)
    (constructed : Satisfies base prior) : Satisfies (CompilerCompletion.run base stages) prior := by
  intro row member
  have preserved (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (CompilerCompletion.run base stages) terms = eval base terms := by
    apply PoseidonCompletion.eval_run_preserves
    intro term present
    exact outside row member term (inside term present)
  rw [preserved row.a (by intro term present; exact List.mem_append_left row.b present),
    preserved row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact constructed row member

set_option pp.all true in
#check @lower_origin_certified
#print axioms lower_origin_certified
set_option pp.all true in
#check @fixed_run_support
#print axioms fixed_run_support
set_option pp.all true in
#check @fixed_preserves_constructed_rows
#print axioms fixed_preserves_constructed_rows
set_option pp.all true in
#check @bit_patch_preserves_constructed_rows
#print axioms bit_patch_preserves_constructed_rows
set_option pp.all true in
#check @compiler_preserves_constructed_rows
#print axioms compiler_preserves_constructed_rows

end ShielddSecurity.GroupPrefixFrameTransport
