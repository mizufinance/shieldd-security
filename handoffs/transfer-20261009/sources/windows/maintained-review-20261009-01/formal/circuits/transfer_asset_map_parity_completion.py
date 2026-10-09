"""Native sign normalization constructs the actual map parity/choice slice.

The sqrt selected-square contract and nonzero first cubic imply zero cannot be
the true branch. Canonical parity is then a constructor result. This module
does not establish the comparator endpoint or other map row preservation.
"""
from . import transfer_asset_map as maps, transfer_relation as relation
from . import transfer_asset_map_completion as completion
from .transfer_balance_rows import canonical, combine


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import linear, _signature_audits
    recipe = completion.plan(data, extracted, accepted_roles)
    checked, raw, rows = recipe['checked'], recipe['raw'], recipe['normalized']
    seeds = recipe['seeds'];choice = seeds['choice'];root = seeds['selectedRoot'];start = seeds['bit0']
    completion.generate_native_bits(data, extracted, accepted_roles)
    difference = combine(checked['bits'][0], checked['values']['square'], -1)
    parity = [i for i, row in rows.items() if row in ((difference, ()), (maps._scale(difference, -1), ()))]
    boolean = [i for i, row in rows.items() if row == (((choice, 1),), ((choice, 1),))]
    copy = checked['metadata']['constant_copy']
    link = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(parity) != 1 or len(boolean) != 1 or len(link) != 1:
        raise relation.RelationError('map parity completion exact Boolean/parity/link rows')
    indices = sorted(parity + boolean + link)
    name = 'RuntimeTransferAssetMapParityCompletion';bits = 'RuntimeTransferAssetMapNativeBits'
    source = f'''import ShielddSecurity.{bits}
import ShielddSecurity.ElligatorNativeParity
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact source metadata SHA256 {checked['metadata_sha256']}.
-- Exact root/255 bits/choice/parity slice; comparator and other map rows remain open.
abbrev modulus := {bits}.modulus
def originalLocalRows : List Nat := {indices}
def localRows : List Row := [
''' + ',\n'.join('⟨' + linear(raw[i][0]) + ',' + linear(raw[i][1]) + '⟩' for i in indices) + f''']
def expectedLocalRows : List Row := [booleanRow {choice},equalityRow {start} {choice},⟨[],[]⟩]
def rawRows : List Row := {bits}.rawRows ++ localRows
variable {{F : Type}} [Field F] [CharP F modulus]
def seedChoice (rho : Nat → F) (option : Bool) : Nat → F :=
  patchAssignment rho (fun _ => if option then 1 else 0) [{choice}]
def completeAssignment (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (option : Bool) (root : F) : Nat → F :=
  {bits}.completeAssignment codec (seedChoice rho option)
    (ElligatorNativeParity.normalizeRoot codec option root)

theorem coverage_checked : localRows.all (fun actual =>
    expectedLocalRows.any (fun expected => decide (
      (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
       Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide

theorem coverage : ∀ actual ∈ localRows, ∃ expected ∈ expectedLocalRows,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem preserves (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (option : Bool) (root : F) (column : Nat) (outsideChoice : column ≠ {choice})
    (outsideRoot : column ≠ {root}) (outsideBits : column < {start} ∨ {start}+255 ≤ column) :
    completeAssignment codec rho option root column = rho column := by
  unfold completeAssignment
  rw [{bits}.preserves codec _ _ column outsideRoot outsideBits]
  exact patchAssignment_preserves rho _ [{choice}] column
    (by simpa only [List.mem_singleton] using outsideChoice)

theorem choice_value (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (option : Bool) (root : F) :
    completeAssignment codec rho option root {choice} = if option then 1 else 0 := by
  unfold completeAssignment
  rw [{bits}.preserves codec _ _ {choice} (by decide) (by decide)]
  simp [seedChoice,patchAssignment]

theorem first_bit (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (option : Bool) (root : F) : completeAssignment codec rho option root {start} =
      if decide (codec.decode (ElligatorNativeParity.normalizeRoot codec option root) % 2 = 1)
      then 1 else 0 := by
  unfold completeAssignment {bits}.completeAssignment
  rw [show encodeBits 255 (codec.decode (ElligatorNativeParity.normalizeRoot codec option root)) =
    decide (codec.decode (ElligatorNativeParity.normalizeRoot codec option root) % 2 = 1) ::
      encodeBits 254 (codec.decode (ElligatorNativeParity.normalizeRoot codec option root) / 2) from rfl]
  simp [writeBits]

theorem complete (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (option : Bool) (first alternative root : F) (firstNonzero : first ≠ 0)
    (nativeSquare : root * root = if option then first else alternative)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment codec rho option root) rawRows := by
  have native := ElligatorNativeParity.selected_normalization codec option first alternative root
    firstNonzero nativeSquare
  have low := first_bit codec rho option root
  rw [native.2] at low
  have lowValue : completeAssignment codec rho option root {start} = if option then 1 else 0 := by
    cases option <;> simpa using low
  have choiceValue := choice_value codec rho option root
  have seedLink : seedChoice rho option {copy} = seedChoice rho option 0 := by
    have copyValue : seedChoice rho option {copy} = rho {copy} :=
      patchAssignment_preserves rho _ [{choice}] {copy} (by decide)
    have zeroValue : seedChoice rho option 0 = rho 0 :=
      patchAssignment_preserves rho _ [{choice}] 0 (by decide)
    exact copyValue.trans (linked.trans zeroValue.symm)
  have bitRows := {bits}.complete codec (seedChoice rho option)
    (ElligatorNativeParity.normalizeRoot codec option root) seedLink
  have expected : Satisfies (completeAssignment codec rho option root) expectedLocalRows := by
    intro row member
    simp only [expectedLocalRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · simp only [booleanRow,Square,eval,Int.cast_one,one_mul,add_zero,choiceValue]
      cases option <;> simp
    · simp only [equalityRow,Square,eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,
        add_zero,lowValue,choiceValue]
      ring
    · simp only [Square,eval,zero_mul]
  have copyLink : completeAssignment codec rho option root {copy} =
      completeAssignment codec rho option root 0 := by
    rw [preserves codec rho option root {copy} (by decide) (by decide) (by decide),
      preserves codec rho option root 0 (by decide) (by decide) (by decide),linked]
  have locals := CompilerSignedCompletion.original_rows (completeAssignment codec rho option root)
    expectedLocalRows localRows {copy} copyLink expected coverage
  intro row member
  rcases List.mem_append.mp member with bit | localRow
  · exact bitRows row bit
  · exact locals row localRow
'''
    exports = ['coverage_checked', 'coverage', 'preserves', 'choice_value', 'first_bit', 'complete']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    source += 'end ShielddSecurity.' + name + '\n'
    return name, _signature_audits(source)
