"""Transport shared canonical-column agreement through genuine EPK maps."""
from . import transfer_relation as relation
from .generate_transfer_epk_write_support import _operands
from .generate_hash_round import _signature_audits


def generate(pair):
    entries = pair.get('restricted_map') if isinstance(pair, dict) else None
    if (not isinstance(entries, list) or not entries or
            any(not isinstance(entry, (list, tuple)) or len(entry) != 2 or
                any(type(column) is not int or not 0 <= column < 262144 for column in entry)
                for entry in entries) or
            len({entry[0] for entry in entries}) != len(entries) or
            len({entry[1] for entry in entries}) != len(entries)):
        raise relation.RelationError('genuine finite injective integer column map required')
    scope, writes, inputs, columns = _operands(pair)
    private = columns[4930]
    start = private + 1
    terminal = columns.get(89120)
    expected = {1: (6334, 99447), 2: (11611, 140304),
                3: (13629, 152378), 4: (14891, 159671), 5: (16153, 166964)}
    if (type(private) is not int or type(terminal) is not int or
            (private, terminal) != expected[scope] or
            any(columns.get(4931 + i) != start + i for i in range(252)) or
            any(c not in writes for c in [*range(start, start + 252), terminal])):
        raise relation.RelationError('exact mapped 252 canonical bits and terminal wire required')
    mapping = f'RuntimeTransferEpk{scope}RenamingMap'
    canonical = f'RuntimeTransferEpk{scope}RenamingRows126'
    name = f'RuntimeTransferEpk{scope}SharedCanonical'
    text = f'''import ShielddSecurity.TransferEpkSharedCanonical
import ShielddSecurity.{canonical}

namespace ShielddSecurity.{name}
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

variable {{F : Type}} [Field F] [CharP F Scalar.modulus]

private def pullback (rho : Nat → F) : Nat → F :=
  fun column => rho ({mapping}.columns column)

private theorem mapped_unit : {mapping}.columns 0 = 0 := by decide
private theorem mapped_input : {mapping}.columns 4930 = {private} := by decide
private theorem mapped_terminal : {mapping}.columns 89120 = {terminal} := by decide
private theorem mapped_bits_checked : (List.range 252).all (fun index =>
    decide ({mapping}.columns (4931 + index) = {start} + index)) = true := by decide
private theorem mapped_bit (index : Nat) (bound : index < 252) :
    {mapping}.columns (4931 + index) = {start} + index :=
  of_decide_eq_true (List.all_eq_true.mp mapped_bits_checked index (List.mem_range.mpr bound))

private theorem canonical_rows (rho : Nat → F)
    (satisfied : Satisfies rho {canonical}.rawRows) :
    Satisfies (pullback rho) RuntimeTransferEpk0Canonical.originalRows := by
  exact RowRenaming.satisfied_rows rho {mapping}.columns RuntimeTransferEpk0Canonical.originalRows
    {canonical}.rawRows (by
      intro row member
      rw [{canonical}.exact_rows]
      exact List.mem_map.mpr ⟨row,member,rfl⟩) satisfied

theorem bit_agreement (left right : Nat → F)
    (leftOne : left 0 = 1) (rightOne : right 0 = 1) (four : (4 : F) ≠ 0)
    (leftRows : Satisfies left {canonical}.rawRows)
    (rightRows : Satisfies right {canonical}.rawRows)
    (sameInput : left {private} = right {private}) (index : Nat) (bound : index < 252) :
    left ({start} + index) = right ({start} + index) := by
  have lOne : pullback left 0 = 1 := by simpa only [pullback,mapped_unit] using leftOne
  have rOne : pullback right 0 = 1 := by simpa only [pullback,mapped_unit] using rightOne
  have input : pullback left 4930 = pullback right 4930 := by
    simpa only [pullback,mapped_input] using sameInput
  have same := TransferEpkSharedCanonical.bit_agreement (pullback left) (pullback right)
    lOne rOne four (canonical_rows left leftRows) (canonical_rows right rightRows) input index bound
  simpa only [pullback,mapped_bit index bound] using same

theorem terminal_agreement (left right : Nat → F)
    (leftOne : left 0 = 1) (rightOne : right 0 = 1) (four : (4 : F) ≠ 0)
    (leftRows : Satisfies left {canonical}.rawRows)
    (rightRows : Satisfies right {canonical}.rawRows)
    (sameInput : left {private} = right {private}) : left {terminal} = right {terminal} := by
  have lOne : pullback left 0 = 1 := by simpa only [pullback,mapped_unit] using leftOne
  have rOne : pullback right 0 = 1 := by simpa only [pullback,mapped_unit] using rightOne
  have input : pullback left 4930 = pullback right 4930 := by
    simpa only [pullback,mapped_input] using sameInput
  have same := TransferEpkSharedCanonical.terminal_agreement (pullback left) (pullback right)
    lOne rOne four (canonical_rows left leftRows) (canonical_rows right rightRows) input
  simpa only [pullback,mapped_terminal] using same

theorem preserves_shared_rows (tree : FiniteColumnRenaming.Tree)
    (base built : Nat → F) (rows : List Row)
    (baseOne : base 0 = 1) (builtOne : built 0 = 1) (four : (4 : F) ≠ 0)
    (baseCanonical : Satisfies base {canonical}.rawRows)
    (builtCanonical : Satisfies built {canonical}.rawRows)
    (sameInput : base {private} = built {private})
    (support : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup tree term.1 = none ∨
        (∃ index < 252,term.1 = {start} + index) ∨ term.1 = {terminal})
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

#print axioms bit_agreement
#print axioms terminal_agreement
#print axioms preserves_shared_rows
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
