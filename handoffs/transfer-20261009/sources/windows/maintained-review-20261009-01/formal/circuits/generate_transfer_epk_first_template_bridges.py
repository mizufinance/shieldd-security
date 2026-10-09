"""Reuse actual first-page transports and bridge their repeated row lists."""
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(index):
    if type(index) is not int or not 1 <= index <= 15:
        raise relation.RelationError('exact retained first-page window required')
    original = f'RuntimeTransferEpk1RenamingRows{index:03d}'
    template = f'RuntimeTransferEpk0FixedWindow{index:03d}TemplateCompletion'
    name = f'RuntimeTransferEpk1TemplateRowBridge{index:03d}'
    columns = 'RuntimeTransferEpk1RenamingMap.columns'
    text = f'''import ShielddSecurity.{original}
import ShielddSecurity.{template}
import ShielddSecurity.RowOrientationSoundness
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def rawRows : List Row := {original}.rawRows
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
    return name, _signature_audits(text)
