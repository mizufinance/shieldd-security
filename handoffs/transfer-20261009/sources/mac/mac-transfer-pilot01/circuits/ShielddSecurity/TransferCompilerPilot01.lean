import ShielddSecurity.TransferCompilerPilotData01

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCompilerPilot01
open Compiler CompilerCompletion TransferCompilerPilotData01

/-! This concrete eight-row pilot has an actual typed fourteen-node certificate.
It exercises lowering, a deferred Boolean assertion, both selected input links,
and the outlined constant link. It is not the complete Transfer graph. The
Boolean domain below is a separately declared literal input domain. -/

def kept : List Nat := [0, 1, 2, 9, 10, 16, 17, 22737, copy]

def steps : List Step :=
  [.square [(16,1)] [] 22738,
   .square [(17,1)] [] 22739,
   .product [(22738,coefficient)] [(22739,1)] [] 22740 22741,
   .squareEqual [(10,1)] [(10,1)],
   .equal [(1,1)] [(22737,1)],
   .equal [(2,1)] [(9,1)],
   -- The final original copy row unoutlines to zero. Construction explicitly
   -- sets and preserves both copies, rather than presuming that row satisfied.
   .equal [(0,1)] [(0,1)]]

theorem topological : Topological kept [] steps := by
  simp [Topological, Step.Shape, Step.writes, Step.rows, squareRows,
    ScalarCompletion.productRows, Compiler.subtract, scaleLinear, kept, steps, copy]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro a b member
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := member <;> decide

theorem complete_original_row_coverage :
    ∀ actual ∈ originalRows, ∃ expected ∈ emitted steps,
      canonical p (unoutline copy actual.a) = canonical p expected.a ∧
      canonical p (unoutline copy actual.b) = canonical p expected.b := by
  intro actual member
  simp only [originalRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨[(16,1)], [(22738,1)]⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨[(17,1)], [(22739,1)]⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨[(22738,coefficient), (22739,-1)], [(22741,1)]⟩,
      by decide, by decide, by decide⟩
  · exact ⟨⟨[(22738,coefficient), (22739,1)], [(22741,1), (22740,4)]⟩,
      by decide, by decide, by decide⟩
  · exact ⟨⟨[(10,1)], [(10,1)]⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨[(1,1), (22737,-1)], []⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨[(2,1), (9,-1)], []⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨[(0,1), (0,-1)], []⟩, by decide, by decide, by decide⟩

variable {F : Type} [Field F]

/-- All source inputs remain total; only the pilot's actual fresh materialized
columns are patched. The original selected inputs and fixed constant are set
by this construction, not desired-row-value premises. -/
def boundary (inputs : Nat → F) (column : Nat) : F :=
  if column = 0 ∨ column = copy then 1
  else if column = 1 then inputs 22734
  else if column = 2 then inputs 6
  else if 3 ≤ column ∧ column < 22738 then inputs (column-3)
  else 0

def BooleanInput (inputs : Nat → F) : Prop := inputs 7 = 0 ∨ inputs 7 = 1

theorem legal_of_boolean_input (inputs : Nat → F) (legal : BooleanInput inputs) :
    Legal (boundary inputs) steps := by
  have boolean : inputs 7 * inputs 7 = inputs 7 := by
    rcases legal with zero | one
    · rw [zero]; simp
    · rw [one]; simp
  simpa [Legal, Step.Legal, Step.run, steps, extendSquare,
    ScalarCompletion.extendProduct, patchAssignment, boundary, copy, eval] using boolean

theorem original_input_preserved (inputs : Nat → F) (input : Nat)
    (bound : input < 22735) : run (boundary inputs) steps (3+input) = inputs input := by
  have low : 3 ≤ 3+input := by omega
  have high : 3+input < 22738 := by omega
  have neq0 : 3+input ≠ 0 := by omega
  have neq1 : 3+input ≠ 1 := by omega
  have neq2 : 3+input ≠ 2 := by omega
  have neqCopy : 3+input ≠ copy := by unfold copy; omega
  have outside38 : 3+input ≠ 22738 := by omega
  have outside39 : 3+input ≠ 22739 := by omega
  have outside40 : 3+input ≠ 22740 := by omega
  have outside41 : 3+input ≠ 22741 := by omega
  simp [run, steps, Step.run, extendSquare, ScalarCompletion.extendProduct,
    patchAssignment, boundary, low, high, neq0, neq1, neq2, neqCopy,
    outside38, outside39, outside40, outside41]

theorem constructive_pilot (inputs : Nat → F) (legal : BooleanInput inputs)
    [CharP F p] :
    ∃ rho : Nat → F, rho 0 = 1 ∧ rho copy = 1 ∧
      rho 1 = inputs 22734 ∧ rho 2 = inputs 6 ∧
      (∀ input < 22735, rho (3+input) = inputs input) ∧ Satisfies rho originalRows := by
  have result := original_rows_complete (p := p) (boundary inputs) steps kept
    originalRows copy topological (legal_of_boolean_input inputs legal)
    (by decide) (by decide) (by simp [boundary, copy]) complete_original_row_coverage
  refine ⟨run (boundary inputs) steps, ?_, ?_, ?_, ?_,
    original_input_preserved inputs, result.1⟩
  all_goals rw [result.2 _ (by decide)]; simp [boundary, copy]

variable [CharP F p]

theorem four_nonzero : (4 : F) ≠ 0 := by
  intro zero
  have castZero : ((4 : Nat) : F) = ((0 : Nat) : F) := by simpa using zero
  have congruent := (CharP.cast_eq_iff_mod_eq F p).mp castZero
  have small : 4 < p := by decide
  have impossible : (4 : Nat) = 0 := by
    simpa only [Nat.mod_eq_of_lt small, Nat.zero_mod] using congruent
  omega

theorem copy_and_input_links (rho : Nat → F) (satisfied : Satisfies rho originalRows) :
    rho copy = rho 0 ∧ rho 1 = rho 22737 ∧ rho 2 = rho 9 := by
  have copied := checked_assertion_sound (p := p) rho originalRows
    [(0,1)] [(copy,1)] satisfied (by decide)
  have publicLink := checked_assertion_sound (p := p) rho originalRows
    [(1,1)] [(22737,1)] satisfied (by decide)
  have committed := checked_assertion_sound (p := p) rho originalRows
    [(2,1)] [(9,1)] satisfied (by decide)
  exact ⟨by simpa [eval] using copied.symm,
    by simpa [eval] using publicLink, by simpa [eval] using committed⟩

theorem arbitrary_assignment_graph (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho originalRows) :
    GraphSatisfies graph (fun input => eval rho (inputTerms input))
      (fun index => expressionValue rho (expressions index)) := by
  have unoutlined := unoutline_rows_sound (p := p) rho copy originalRows satisfied (by decide)
  exact graph_certificate_sound graph unoutlinedRows inputTerms expressions
    node_certificates assertion_certificates rho one four_nonzero unoutlined

theorem boolean_consequence (rho : Nat → F) (satisfied : Satisfies rho originalRows) :
    rho 10 = 0 ∨ rho 10 = 1 := by
  have row := checked_row_sound (p := p) rho originalRows
    ⟨[(10,1)], [(10,1)]⟩ satisfied (by decide)
  apply boolean_sound
  simpa [eval] using row

theorem illegal_boolean_refused (rho : Nat → F)
    (nonzero : rho 10 ≠ 0) (nonone : rho 10 ≠ 1) : ¬ Satisfies rho originalRows := by
  intro satisfied
  rcases boolean_consequence rho satisfied with zero | one
  · exact nonzero zero
  · exact nonone one

/-! Exact full-capture indexing remains explicit until complete block
composition supplies its concrete instance. This transport performs indexed
membership, never a scan over the whole relation for each local row. -/
def capturedEntries : List (Nat × Row) := captureIndices.zip originalRows

def ExactIndexedInstance (fullRows : List Row) : Prop :=
  ∀ entry ∈ capturedEntries, fullRows[entry.1]? = some entry.2

theorem local_projection (fullRows : List Row) (identity : ExactIndexedInstance fullRows)
    (rho : Nat → F) (satisfied : Satisfies rho fullRows) : Satisfies rho originalRows := by
  intro row member
  simp only [originalRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply satisfied
  · exact List.mem_of_getElem? (identity (0, _) (by decide))
  · exact List.mem_of_getElem? (identity (1, _) (by decide))
  · exact List.mem_of_getElem? (identity (2, _) (by decide))
  · exact List.mem_of_getElem? (identity (3, _) (by decide))
  · exact List.mem_of_getElem? (identity (177954, _) (by decide))
  · exact List.mem_of_getElem? (identity (200767, _) (by decide))
  · exact List.mem_of_getElem? (identity (200768, _) (by decide))
  · exact List.mem_of_getElem? (identity (200769, _) (by decide))

end ShielddSecurity.TransferCompilerPilot01

set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.topological
#print axioms ShielddSecurity.TransferCompilerPilot01.topological
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.complete_original_row_coverage
#print axioms ShielddSecurity.TransferCompilerPilot01.complete_original_row_coverage
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.legal_of_boolean_input
#print axioms ShielddSecurity.TransferCompilerPilot01.legal_of_boolean_input
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.original_input_preserved
#print axioms ShielddSecurity.TransferCompilerPilot01.original_input_preserved
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.constructive_pilot
#print axioms ShielddSecurity.TransferCompilerPilot01.constructive_pilot
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.four_nonzero
#print axioms ShielddSecurity.TransferCompilerPilot01.four_nonzero
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.copy_and_input_links
#print axioms ShielddSecurity.TransferCompilerPilot01.copy_and_input_links
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.arbitrary_assignment_graph
#print axioms ShielddSecurity.TransferCompilerPilot01.arbitrary_assignment_graph
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.boolean_consequence
#print axioms ShielddSecurity.TransferCompilerPilot01.boolean_consequence
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.illegal_boolean_refused
#print axioms ShielddSecurity.TransferCompilerPilot01.illegal_boolean_refused
set_option pp.all true in
#check @ShielddSecurity.TransferCompilerPilot01.local_projection
#print axioms ShielddSecurity.TransferCompilerPilot01.local_projection
