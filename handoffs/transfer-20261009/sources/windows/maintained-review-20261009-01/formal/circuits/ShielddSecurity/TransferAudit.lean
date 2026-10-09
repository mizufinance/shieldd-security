import ShielddSecurity.TransferMixedBody

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferAudit

/-!
Independent TransferOutput audit emission. M is the entire metadata value,
not its digest. The carrier retains complete ciphertext and asset anchor.
The caller supplies the original mixed action ordinal, not a filtered index.
Native codecs, audit-record validation, source transaction identity, ordered
state append and persistence are explicit source refinement boundaries.
-/

structure Output (M : Type) where
  assetAnchor : Nat
  ciphertext : List Nat
  metadata : M

structure Record (M : Type) where
  height : Nat
  transaction : Nat
  actionIndex : Nat
  effectIndex : Nat
  output : Output M

def kept {M : Type} (outputs : List (Output M)) : List (Output M) :=
  outputs.filter fun output => decide (output.ciphertext ≠ [])

def collect {M : Type} (height transaction actionIndex start : Nat) :
    List (Output M) → List (Record M)
  | [] => []
  | output :: rest =>
      if output.ciphertext = [] then collect height transaction actionIndex start rest
      else ⟨height, transaction, actionIndex, start, output⟩ ::
        collect height transaction actionIndex (start + 1) rest

theorem output_selection {M : Type} (height transaction actionIndex start : Nat)
    (outputs : List (Output M)) :
    (collect height transaction actionIndex start outputs).map Record.output = kept outputs := by
  induction outputs generalizing start with
  | nil => rfl
  | cons output rest ih =>
    by_cases empty : output.ciphertext = []
    · simp [collect, kept, empty, ih]
    · simp [collect, kept, empty, ih]

theorem emitted_count {M : Type} (height transaction actionIndex start : Nat)
    (outputs : List (Output M)) :
    (collect height transaction actionIndex start outputs).length = (kept outputs).length := by
  have selected := congrArg List.length (output_selection height transaction actionIndex start outputs)
  simpa only [List.length_map] using selected

theorem emitted_count_bound {M : Type} (height transaction actionIndex start : Nat)
    (outputs : List (Output M)) :
    (collect height transaction actionIndex start outputs).length ≤ outputs.length := by
  rw [emitted_count]
  exact List.length_filter_le _ _

theorem record_source_and_index {M : Type} (height transaction actionIndex start : Nat)
    (outputs : List (Output M)) (record : Record M)
    (inside : record ∈ collect height transaction actionIndex start outputs) :
    record.height = height ∧ record.transaction = transaction ∧ record.actionIndex = actionIndex ∧
      start ≤ record.effectIndex ∧
      record.effectIndex < start + (collect height transaction actionIndex start outputs).length ∧
      record.output ∈ outputs ∧ record.output.ciphertext ≠ [] := by
  induction outputs generalizing start with
  | nil => simp only [collect, List.not_mem_nil] at inside
  | cons output rest ih =>
    by_cases empty : output.ciphertext = []
    · simp only [collect, if_pos empty] at inside ⊢
      have retained := ih start inside
      exact ⟨retained.1, retained.2.1, retained.2.2.1, retained.2.2.2.1,
        retained.2.2.2.2.1, List.mem_cons_of_mem _ retained.2.2.2.2.2.1,
        retained.2.2.2.2.2.2⟩
    · simp only [collect, if_neg empty, List.length_cons] at inside ⊢
      rcases List.mem_cons.mp inside with same | later
      · subst record
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, by dsimp only; omega, List.mem_cons_self, empty⟩
      · have retained := ih (start + 1) later
        refine ⟨retained.1, retained.2.1, retained.2.2.1, ?_, ?_,
          List.mem_cons_of_mem _ retained.2.2.2.2.2.1, retained.2.2.2.2.2.2⟩
        · have lower := retained.2.2.2.1
          omega
        · have upper := retained.2.2.2.2.1
          omega

theorem second_output_dense_zero {M : Type} (height transaction actionIndex : Nat)
    (first second : Output M) (empty : first.ciphertext = [])
    (present : second.ciphertext ≠ []) :
    collect height transaction actionIndex 0 [first, second] =
      [⟨height, transaction, actionIndex, 0, second⟩] := by
  simp only [collect, if_pos empty, if_neg present]

theorem two_outputs_in_order {M : Type} (height transaction actionIndex : Nat)
    (first second : Output M) (firstPresent : first.ciphertext ≠ [])
    (secondPresent : second.ciphertext ≠ []) :
    collect height transaction actionIndex 0 [first, second] =
      [⟨height, transaction, actionIndex, 0, first⟩,
        ⟨height, transaction, actionIndex, 1, second⟩] := by
  simp only [collect, if_neg firstPresent, if_neg secondPresent, Nat.zero_add]

theorem duplicate_outputs_preserved {M : Type} (height transaction actionIndex : Nat)
    (output : Output M) (present : output.ciphertext ≠ []) :
    (collect height transaction actionIndex 0 [output, output]).map Record.output = [output, output] := by
  rw [two_outputs_in_order height transaction actionIndex output output present present]
  rfl

theorem two_empty_outputs {M : Type} (height transaction actionIndex : Nat)
    (first second : Output M) (firstEmpty : first.ciphertext = [])
    (secondEmpty : second.ciphertext = []) :
    collect height transaction actionIndex 0 [first, second] = [] := by
  simp only [collect, if_pos firstEmpty, if_pos secondEmpty]

theorem fixed_outputs_index_u32 {M : Type} (height transaction actionIndex : Nat)
    (first second : Output M) (record : Record M)
    (inside : record ∈ collect height transaction actionIndex 0 [first, second]) :
    record.effectIndex < 2 ^ 32 := by
  have indexed := (record_source_and_index height transaction actionIndex 0 [first, second] record inside).2.2.2.2.1
  have bounded := emitted_count_bound height transaction actionIndex 0 [first, second]
  have capacity : 2 < 2 ^ 32 := by decide
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at indexed bounded
  omega

set_option pp.all true in
#check @output_selection
#print axioms output_selection
set_option pp.all true in
#check @emitted_count
#print axioms emitted_count
set_option pp.all true in
#check @emitted_count_bound
#print axioms emitted_count_bound
set_option pp.all true in
#check @record_source_and_index
#print axioms record_source_and_index
set_option pp.all true in
#check @second_output_dense_zero
#print axioms second_output_dense_zero
set_option pp.all true in
#check @two_outputs_in_order
#print axioms two_outputs_in_order
set_option pp.all true in
#check @duplicate_outputs_preserved
#print axioms duplicate_outputs_preserved
set_option pp.all true in
#check @two_empty_outputs
#print axioms two_empty_outputs
set_option pp.all true in
#check @fixed_outputs_index_u32
#print axioms fixed_outputs_index_u32

end ShielddSecurity.TransferAudit
