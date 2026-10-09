import ShielddSecurity.Compiler
import ShielddSecurity.TransferBalance

set_option maxHeartbeats 400000

namespace ShielddSecurity.TransferBalanceRows
open Compiler TransferCore TransferBalance

/-- A small selected range block is interpreted over arbitrary assignments.
The Boolean rows are actual literal data; the equality and reconstruction
certificates are checked by coefficient normalization, not digest identity. -/
theorem selected_range_sound {F : Type} [Field F] [CharP F fieldModulus]
    (rho : Nat → F) (actualBooleans : List Row) (actualReconstruction : Row)
    (value : Linear) (bits : List Nat)
    (booleanIdentity : actualBooleans = bits.map booleanRow)
    (reconstruction : checkRow fieldModulus [actualReconstruction]
      (expressionReconstructionRow value bits) = true)
    (satisfied : Satisfies rho (actualBooleans ++ [actualReconstruction])) :
    ∃ n : Nat, n < 2 ^ bits.length ∧ (n : F) = eval rho value := by
  have booleans : ∀ x ∈ bits.map rho, Square x x := by
    intro x member
    obtain ⟨column, present, rfl⟩ := List.mem_map.mp member
    have row : booleanRow column ∈ actualBooleans ++ [actualReconstruction] := by
      rw [booleanIdentity]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨column, present, rfl⟩)
    simpa [booleanRow, eval] using satisfied _ row
  have only : Satisfies rho [actualReconstruction] := by
    intro row present
    exact satisfied row (List.mem_append_right _ present)
  have checked := checked_row_sound rho [actualReconstruction]
    (expressionReconstructionRow value bits) only reconstruction
  have zero : eval rho (expressionReconstructionRow value bits).a = 0 := by
    exact square_zero _ (by simpa [expressionReconstructionRow, eval] using checked)
  have rebuilt : fieldBinary (bits.map rho) = eval rho value := by
    apply sub_eq_zero.mp
    simpa [expressionReconstructionRow, eval_append, weighted_eval, eval_scale,
      eval, sub_eq_add_neg] using zero
  simpa using range_sound (bits.map rho) (eval rho value) booleans rebuilt

set_option pp.all true in
#check @selected_range_sound
#print axioms selected_range_sound

end ShielddSecurity.TransferBalanceRows
