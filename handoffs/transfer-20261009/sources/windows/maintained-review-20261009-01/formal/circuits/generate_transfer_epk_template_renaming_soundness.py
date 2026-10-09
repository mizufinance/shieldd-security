"""Bidirectional physical row satisfaction, preserving repeated copy links."""
import re
from . import generate_transfer_epk_template_renaming_rows as basis
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(name, source):
    name, adapted = basis.generate(name, source)
    marker = '\ntheorem exact_rows : '
    if adapted.count(marker) != 1:
        raise relation.RelationError('exact local equality source boundary required')
    prefix = adapted.split(marker)[0]
    if not prefix.startswith('import ShielddSecurity.RuntimeTransferEpk1RenamingMap\n'):
        raise relation.RelationError('original scope-one transport map required')
    prefix = 'import ShielddSecurity.RowOrientationSoundness\n' + prefix
    template = 'RuntimeTransferEpk0FixedWindow' + name[-3:] + 'TemplateCompletion'
    columns = 'RuntimeTransferEpk1RenamingMap.columns'
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
