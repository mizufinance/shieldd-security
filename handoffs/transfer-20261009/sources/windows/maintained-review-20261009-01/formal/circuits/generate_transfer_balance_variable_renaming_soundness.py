"""Reverse physical-row checks and arbitrary-assignment local soundness."""
from . import transfer_balance_variable_renaming as matching
from . import generate_transfer_balance_variable_renaming as original
from . import generate_transfer_balance_variable_sequence as sequence
from .generate_hash_round import _signature_audits


def generate(accepted, signed, page_ordinal):
    matching.relation.natural(page_ordinal, 5)
    kept = sequence._kept(accepted, signed)
    result = []
    for item in accepted['programs']:
        if item['page_ordinal'] != page_ordinal or item['index'] < 2:
            continue
        match = matching._pair(accepted, 1, item['index'])
        program, original_source = original._source(accepted, item, match, kept)
        name = program + 'Soundness'
        template = 'RuntimeBalanceVariableWindow001Program'
        source = f'''import ShielddSecurity.{program}
import ShielddSecurity.GroupCircuitRenamingSoundness
import ShielddSecurity.RuntimeBalanceVariableProgramSoundness
import ShielddSecurity.RowOrientationSoundness
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem reverse_rows_checked (lowBit highBit : Bool) :
    ({program}.mappedProgram lowBit highBit).rows.all (fun row =>
      Compiler.checkRow {program}.modulus {program}.actualRows row ||
      Compiler.checkRow {program}.modulus {program}.actualRows
        ⟨scaleLinear (-1) row.a,row.b⟩) = true := by
  change ({program}.mappedProgram false false).rows.all (fun row =>
      Compiler.checkRow {program}.modulus {program}.actualRows row ||
      Compiler.checkRow {program}.modulus {program}.actualRows
        ⟨scaleLinear (-1) row.a,row.b⟩) = true
  decide

theorem local_sound {{F : Type}} [Field F] [CharP F {program}.modulus]
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({program}.d : F))
    (imaginarySquare : imaginary * imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitSoundness.LocalSound ({program}.d : F) 200692
      {program}.tables ({program}.program lowBit highBit) := by
  have fields := {program}.fields_checked lowBit highBit
  have reused := GroupCircuitRenamingSoundness.local_sound {program}.columns
    (by decide) 200692 (by decide) ({program}.d : F)
    {template}.tables ({template}.program lowBit highBit)
    (RuntimeBalanceVariableProgramSoundness.later four imaginary nonSquare imaginarySquare lowBit highBit)
  intro rho one linked incoming curved low high satisfied
  have sourceIncoming : Group.OnCurve ({program}.d : F)
      (GroupFixedCircuitCompletion.point rho ({program}.mappedProgram lowBit highBit).input) := by
    rw [← fields.2.1]; exact incoming
  have sourceCurved : GroupVariableCircuitCompletion.Curved ({program}.d : F)
      (GroupCircuitRenaming.tables {program}.columns {template}.tables) rho := by
    rw [← fields.2.2.2.2.2]; exact curved
  have sourceLow : eval rho ({program}.mappedProgram lowBit highBit).low = if lowBit then 1 else 0 := by
    rw [← fields.2.2.2.1]; exact low
  have sourceHigh : eval rho ({program}.mappedProgram lowBit highBit).high = if highBit then 1 else 0 := by
    rw [← fields.2.2.2.2.1]; exact high
  have sourceRows : Satisfies rho ({program}.mappedProgram lowBit highBit).rows :=
    RowOrientationSoundness.checked_rows rho {program}.actualRows _
      (reverse_rows_checked lowBit highBit) satisfied
  have result := reused rho one linked sourceIncoming sourceCurved sourceLow sourceHigh sourceRows
  change GroupFixedCircuitCompletion.point rho ({program}.program lowBit highBit).output = _
  rw [fields.2.2.1,fields.2.1,fields.2.2.2.1,fields.2.2.2.2.1,fields.2.2.2.2.2]
  exact result
#print axioms reverse_rows_checked
#print axioms local_sound
end ShielddSecurity.{name}
'''
        result.append((name, _signature_audits(source), program, original_source))
    if not result:
        raise matching.relation.RelationError('nonempty bounded renamed soundness page')
    return result
