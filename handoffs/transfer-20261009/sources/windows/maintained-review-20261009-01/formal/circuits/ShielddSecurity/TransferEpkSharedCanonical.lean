import ShielddSecurity.TransferEpkCanonicalReflection
import ShielddSecurity.FiniteWritePatch

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkSharedCanonical

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Two arbitrary row-satisfying canonical words with the same input have
the same integer. Neither assignment is assumed to be an honest witness. -/
theorem integer_agreement (left right : Nat → F)
    (leftOne : left 0 = 1) (rightOne : right 0 = 1) (four : (4 : F) ≠ 0)
    (leftRows : Satisfies left RuntimeTransferEpk0Canonical.originalRows)
    (rightRows : Satisfies right RuntimeTransferEpk0Canonical.originalRows)
    (sameInput : left 4930 = right 4930) :
    binary (RuntimeTransferEpk0Canonical.decodedBits left) =
      binary (RuntimeTransferEpk0Canonical.decodedBits right) := by
  have l := RuntimeTransferEpk0Canonical.actual_randomizer_bits left leftOne four leftRows
  have r := RuntimeTransferEpk0Canonical.actual_randomizer_bits right rightOne four rightRows
  have same : eval left RuntimeTransferEpk0Canonical.privateValue =
      eval right RuntimeTransferEpk0Canonical.privateValue := by
    simpa only [RuntimeTransferEpk0Canonical.privateValue,eval,Int.cast_one,one_mul,add_zero] using sameInput
  exact Scalar.canonical_representative_unique _ _ _
    (l.1.trans (by decide : Scalar.order < Scalar.modulus))
    (r.1.trans (by decide : Scalar.order < Scalar.modulus)) l.2 (r.2.trans same.symm)

/-- All 252 shared bit columns agree by reflection and canonical uniqueness,
without enumerating the bits or assuming their desired values. -/
theorem bit_agreement (left right : Nat → F)
    (leftOne : left 0 = 1) (rightOne : right 0 = 1) (four : (4 : F) ≠ 0)
    (leftRows : Satisfies left RuntimeTransferEpk0Canonical.originalRows)
    (rightRows : Satisfies right RuntimeTransferEpk0Canonical.originalRows)
    (sameInput : left 4930 = right 4930) (index : Nat) (bound : index < 252) :
    left (4931 + index) = right (4931 + index) := by
  have same := integer_agreement left right leftOne rightOne four leftRows rightRows sameInput
  have l := TransferEpkCanonicalReflection.source_bit_value left leftRows index bound
  have r := TransferEpkCanonicalReflection.source_bit_value right rightRows index bound
  rw [same] at l
  have values := l.trans r.symm
  simpa only [eval,Int.cast_one,one_mul,add_zero] using values

private def terminalRows : List Row :=
  unoutlineRows RuntimeTransferEpk0Canonical.copyColumn RuntimeTransferEpk0Canonical.tailRaw

private theorem terminalChecked : ScalarComparisonBounds.checkEquality
    RuntimeTransferEpk0Canonical.p terminalRows [(5182,1)] [(89120,1)] = true := by
  decide

/-- The additional shared comparator wire is fixed by its actual tail row;
the whole comparison walk need not be unrolled again. -/
theorem terminal_agreement (left right : Nat → F)
    (leftOne : left 0 = 1) (rightOne : right 0 = 1) (four : (4 : F) ≠ 0)
    (leftRows : Satisfies left RuntimeTransferEpk0Canonical.originalRows)
    (rightRows : Satisfies right RuntimeTransferEpk0Canonical.originalRows)
    (sameInput : left 4930 = right 4930) : left 89120 = right 89120 := by
  have tail (rho : Nat → F) (satisfied : Satisfies rho RuntimeTransferEpk0Canonical.originalRows) :
      Satisfies rho terminalRows := by
    have allRows := Compiler.unoutline_rows_sound rho RuntimeTransferEpk0Canonical.copyColumn
      RuntimeTransferEpk0Canonical.originalRows satisfied RuntimeTransferEpk0Canonical.checked_copy
    intro row member
    exact allRows row (RuntimeTransferEpk0Canonical.tail_included row member)
  have l := ScalarComparisonBounds.checked_equality left terminalRows (tail left leftRows)
    [(5182,1)] [(89120,1)] terminalChecked
  have r := ScalarComparisonBounds.checked_equality right terminalRows (tail right rightRows)
    [(5182,1)] [(89120,1)] terminalChecked
  have last := bit_agreement left right leftOne rightOne four leftRows rightRows sameInput 251 (by decide)
  simp only [eval,Int.cast_one,one_mul,add_zero] at l r
  exact l.symm.trans (last.trans r)

/-- A patch may overlap prior rows on these 253 canonical columns. Actual
support classification and both canonical row blocks are required separately;
the shared-column equalities themselves are derived above. -/
theorem preserves_shared_rows (tree : FiniteColumnRenaming.Tree)
    (base built : Nat → F) (rows : List Row)
    (baseOne : base 0 = 1) (builtOne : built 0 = 1) (four : (4 : F) ≠ 0)
    (baseCanonical : Satisfies base RuntimeTransferEpk0Canonical.originalRows)
    (builtCanonical : Satisfies built RuntimeTransferEpk0Canonical.originalRows)
    (sameInput : base 4930 = built 4930)
    (support : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup tree term.1 = none ∨
        (∃ index < 252,term.1 = 4931 + index) ∨ term.1 = 89120)
    (satisfied : Satisfies base rows) :
    Satisfies (FiniteWritePatch.assignment tree base built) rows := by
  intro row member
  have agrees (terms : Linear) (included : ∀ term ∈ terms,term ∈ row.a ++ row.b) :
      eval (FiniteWritePatch.assignment tree base built) terms = eval base terms := by
    apply eval_agrees
    intro term present
    rcases support row member term (included term present) with outside | bit | terminal
    · exact FiniteWritePatch.preserves tree base built term.1 outside
    · obtain ⟨index,bound,column⟩ := bit
      have same : built term.1 = base term.1 := by
        rw [column]
        exact (bit_agreement base built baseOne builtOne four baseCanonical builtCanonical sameInput index bound).symm
      unfold FiniteWritePatch.assignment
      split
      · exact same
      · rfl
    · have same : built term.1 = base term.1 := by
        rw [terminal]
        exact (terminal_agreement base built baseOne builtOne four baseCanonical builtCanonical sameInput).symm
      unfold FiniteWritePatch.assignment
      split
      · exact same
      · rfl
  rw [agrees row.a (by intro term present;exact List.mem_append_left _ present),
    agrees row.b (by intro term present;exact List.mem_append_right _ present)]
  exact satisfied row member

set_option pp.all true in
#check @integer_agreement
#print axioms integer_agreement
set_option pp.all true in
#check @bit_agreement
#print axioms bit_agreement
set_option pp.all true in
#check @terminal_agreement
#print axioms terminal_agreement
set_option pp.all true in
#check @preserves_shared_rows
#print axioms preserves_shared_rows

end ShielddSecurity.TransferEpkSharedCanonical
