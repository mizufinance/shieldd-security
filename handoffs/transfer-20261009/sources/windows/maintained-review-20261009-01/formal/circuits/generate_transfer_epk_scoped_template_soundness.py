"""Local satisfaction transports from each genuine captured EPK scope.

The source recipe accepts the captured source before calling this renderer.
This renderer keeps the exact physical row bodies and finite index lists,
and changes only the proof basis to the audited template definitions.
"""
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(name, source):
    match = re.fullmatch(r'RuntimeTransferEpk([2-5])RenamingRows(\d{3})', name)
    if match is None or not 1 <= int(match[2]) < 126:
        raise relation.RelationError('exact captured remaining-scope ordinary window required')
    scope, index = match.groups()
    old = 'RuntimeTransferEpk0FixedWindow' + index
    template = old + 'TemplateCompletion'
    columns = f'RuntimeTransferEpk{scope}RenamingMap.columns'
    marker = '\ntheorem exact_rows : '
    expected_import = 'import ShielddSecurity.' + old + '\n'
    expected_basis = 'ShielddSecurity.' + old + '.rawRows.map '
    if (source.count(marker) != 1 or source.count(expected_import) != 1
            or source.count(expected_basis) != 1 or source.count(old) != 2
            or source.count(f'namespace ShielddSecurity.{name}\n') != 1
            or not source.startswith(f'import ShielddSecurity.RuntimeTransferEpk{scope}RenamingMap\n')):
        raise relation.RelationError('exact captured map, namespace and physical row boundary required')
    prefix = source.split(marker)[0].replace(expected_import,
        'import ShielddSecurity.' + template + '\n')
    if len(re.findall(r'^def originalRows : List Nat := \[.*\]$', prefix, re.M)) != 1:
        raise relation.RelationError('exact captured physical indices required')
    prefix = 'import ShielddSecurity.RowOrientationSoundness\n' + prefix
    suffix = f'''
def mappedRows : List Row := {template}.rawRows.map (RowRenaming.row {columns})

theorem source_rows_checked : mappedRows.all (fun row =>
    Compiler.checkRow {template}.modulus rawRows row ||
    Compiler.checkRow {template}.modulus rawRows ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

theorem target_rows_checked : rawRows.all (fun row =>
    Compiler.checkRow {template}.modulus mappedRows row ||
    Compiler.checkRow {template}.modulus mappedRows ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

theorem source_satisfied {{F : Type}} [Field F] [CharP F {template}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => rho ({columns} column)) {template}.rawRows := by
  have mapped : Satisfies rho mappedRows :=
    RowOrientationSoundness.checked_rows rho rawRows mappedRows source_rows_checked satisfied
  apply RowRenaming.satisfied_rows rho {columns} {template}.rawRows mappedRows
  · intro item member
    exact List.mem_map.mpr ⟨item,member,rfl⟩
  · exact mapped

theorem target_satisfied {{F : Type}} [Field F] [CharP F {template}.modulus]
    (rho : Nat → F)
    (satisfied : Satisfies (fun column => rho ({columns} column)) {template}.rawRows) :
    Satisfies rho rawRows := by
  have mapped : Satisfies rho mappedRows := by
    intro row member
    obtain ⟨item,present,rfl⟩ := List.mem_map.mp member
    simpa only [RowRenaming.row,RowRenaming.eval_linear] using satisfied item present
  exact RowOrientationSoundness.checked_rows rho mappedRows rawRows target_rows_checked mapped

#print axioms source_rows_checked
#print axioms target_rows_checked
#print axioms source_satisfied
#print axioms target_satisfied
end ShielddSecurity.{name}
'''
    return name, _signature_audits(prefix + suffix)
