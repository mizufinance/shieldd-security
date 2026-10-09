"""Preserve the actual constructed map while writing its separate x inverse.

The constructor for the inverse assertion still needs native legal admission.
This module supplies the same-assignment frame, with bounded existing row
chunks and symbolic bit support. It never takes earlier-row truth as input.
"""
from . import transfer_asset_map_native_completion as native
from . import transfer_asset_generator_nonidentity as inverse
from . import transfer_relation as relation
from . import transfer_asset_map_materialization_sequence as numeric_sequence
from . import transfer_asset_map_comparator_completion as comparator


def plan(data, extracted, inverse_data, inverse_extracted, accepted_roles):
    mapped = native.plan(data, extracted, accepted_roles)
    admitted = inverse.completion_plan(inverse_data, inverse_extracted, accepted_roles)
    view = inverse.derived_map_view(inverse_data, accepted_roles)
    if view['map_data'] != data:
        raise relation.RelationError('map/inverse exact qualified parent projection')
    writes = admitted['writes']
    copy = mapped['recipe']['checked']['metadata']['constant_copy']
    quotient = admitted['quotient']
    floor = min(admitted['product'], admitted['auxiliary'])
    if len(writes) != 3 or len(set(writes)) != 3 or copy in writes:
        raise relation.RelationError('map/inverse exact independent three writes')
    raw = mapped['recipe']['raw']
    for row in raw.values():
        for column, _ in row[0] + row[1]:
            if column in writes or not (column == copy or column < floor):
                raise relation.RelationError('map/inverse original support overlaps new inverse')
    if set(mapped['recipe']['owned_writes']) & set(writes):
        raise relation.RelationError('map/inverse owned assignment overlap')
    return dict(map=mapped, inverse=admitted, writes=writes, copy=copy,
                floor=floor, quotient=quotient,
                numeric_parts=len(numeric_sequence.plan(data, extracted, accepted_roles)['parts']),
                comparator_parts=len(comparator.plan(data, extracted, accepted_roles)['chunks']))


def generate(data, extracted, inverse_data, inverse_extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    result = plan(data, extracted, inverse_data, inverse_extracted, accepted_roles)
    name = 'RuntimeTransferAssetMapInverseFrame'
    whole = 'RuntimeTransferAssetMapNativeCompletion'
    inv = 'RuntimeTransferAssetGeneratorInverseCompletion'
    seq = 'RuntimeTransferAssetMapCanonicalSequence'
    numeric = 'RuntimeTransferAssetMapNumericConstruction'
    canonical = 'RuntimeTransferAssetMapCanonicalConstruction'
    copy, floor, quotient = (result[k] for k in ('copy', 'floor', 'quotient'))
    bits = result['map']['recipe']['checked']['bits']
    start = result['map']['recipe']['seeds']['bit0']
    if len(bits) != 255:
        raise relation.RelationError('map inverse frame canonical255 width')
    parts = [('numeric', [f'RuntimeTransferAssetMapMaterialization{i}' for i in range(result['numeric_parts'])],
              numeric + '.rawChunks'),
             ('comparator', [f'RuntimeTransferAssetMapComparatorConstruction{i}' for i in range(result['comparator_parts'])],
              canonical + '.productOriginalChunks')]
    other = ['RuntimeTransferAssetMapSeedAssertions', 'RuntimeTransferAssetMapNativeFirstRows',
             'RuntimeTransferAssetMapNativeRootRows', 'RuntimeTransferAssetMapNativeRationalRows',
             *[f'RuntimeTransferAssetMapNativeDouble{i}' for i in range(3)]]
    source = f'''import ShielddSecurity.{whole}
import ShielddSecurity.{inv}
import ShielddSecurity.CompilerSequenceCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact map870 physical rows, independent inverse3, same qualified parent.
-- Supports use bounded existing row declarations; no cartesian row/write walk.
abbrev modulus := {whole}.modulus
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev mapAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {whole}.completeAssignment codec api rho
def completeAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : Nat → F :=
  {inv}.completeAssignment (mapAssignment codec api rho)
theorem writes_checked : CompilerSequenceCompletion.checkWrites {copy} {floor} [{quotient}] {inv}.ownedWrites = true := by decide
theorem checked_support (rows : List Row)
    (checked : CompilerSequenceCompletion.checkRows {copy} {floor} [{quotient}] rows = true) :
    ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ {inv}.ownedWrites :=
  CompilerSequenceCompletion.frame_rows {copy} {floor} [{quotient}] {inv}.ownedWrites rows writes_checked checked
'''
    exports = ['writes_checked', 'checked_support']
    for label, modules, chunks in parts:
        for i, module in enumerate(modules):
            export = f'{label}_checked{i}'
            source += f'theorem {export} : CompilerSequenceCompletion.checkRows {copy} {floor} [{quotient}] {module}.rawRows = true := by decide\n'
            exports.append(export)
        rowset = numeric + '.rawRows' if label == 'numeric' else canonical + '.productOriginalChunks.flatten'
        source += f'''theorem {label}_outside : ∀ row ∈ {rowset},
    ∀ term ∈ row.a ++ row.b, term.1 ∉ {inv}.ownedWrites := by
  intro row member term present
  obtain ⟨chunk,inChunks,inChunk⟩ := List.mem_flatten.mp member
  simp only [{chunks},List.mem_cons,List.not_mem_nil,or_false] at inChunks
  rcases inChunks with ''' + ' | '.join(f'case{i}' for i in range(len(modules))) + '\n'
        for i, module in enumerate(modules):
            source += f'  · subst chunk; exact checked_support {module}.rawRows {label}_checked{i} row inChunk term present\n'
        exports.append(label + '_outside')
    source += f'''theorem bit_rows_outside : ∀ row ∈ (List.range' {start} 255).map booleanRow,
    ∀ term ∈ row.a ++ row.b, term.1 ∉ {inv}.ownedWrites := by
  intro row member term present
  obtain ⟨column,inRange,equal⟩ := List.mem_map.mp member
  subst row
  have bounds := List.mem_range'.mp inRange
  have same : term = (column, (1 : Int)) := by
    simpa only [booleanRow,List.singleton_append,List.mem_cons,List.not_mem_nil,or_false,or_self] using present
  subst term
  change column ∉ {result['writes']}
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  omega
theorem boundary_checked : CompilerSequenceCompletion.checkRows {copy} {floor} [{quotient}] {canonical}.boundaryRawRows = true := by decide
theorem canonical_outside : ∀ row ∈ {canonical}.rawRows,
    ∀ term ∈ row.a ++ row.b, term.1 ∉ {inv}.ownedWrites := by
  intro row member term present
  simp only [{canonical}.rawRows,List.mem_append] at member
  rcases member with boolean | products | boundary
  · exact bit_rows_outside row boolean term present
  · exact comparator_outside row products term present
  · exact checked_support _ boundary_checked row boundary term present
theorem sequence_outside : ∀ row ∈ {seq}.rawRows,
    ∀ term ∈ row.a ++ row.b, term.1 ∉ {inv}.ownedWrites := by
  intro row member term present
  rcases List.mem_append.mp member with numerical | canonical
  · exact numeric_outside row numerical term present
  · exact canonical_outside row canonical term present
'''
    exports += ['bit_rows_outside', 'boundary_checked', 'canonical_outside', 'sequence_outside']
    for i, module in enumerate(other):
        source += f'theorem other_checked{i} : CompilerSequenceCompletion.checkRows {copy} {floor} [{quotient}] {module}.rawRows = true := by decide\n'
        exports.append('other_checked' + str(i))
    source += f'''theorem map_outside : ∀ row ∈ {whole}.rawRows,
    ∀ term ∈ row.a ++ row.b, term.1 ∉ {inv}.ownedWrites := by
  intro row member term present
  obtain ⟨chunk,inChunks,inChunk⟩ := List.mem_flatten.mp member
  simp only [{whole}.rawChunks,List.mem_cons,List.not_mem_nil,or_false] at inChunks
  rcases inChunks with ''' + ' | '.join(f'case{i}' for i in range(8)) + '\n'
    source += '  · subst chunk; exact sequence_outside row inChunk term present\n'
    for i, module in enumerate(other):
        source += f'  · subst chunk; exact checked_support {module}.rawRows other_checked{i} row inChunk term present\n'
    source += f'''theorem map_rows_complete [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment codec api rho) {whole}.rawRows := by
  intro row member
  have left : eval (completeAssignment codec api rho) row.a = eval (mapAssignment codec api rho) row.a := by
    apply eval_agrees
    intro term present
    exact {inv}.preserves _ term.1 (map_outside row member term (List.mem_append_left _ present))
  have right : eval (completeAssignment codec api rho) row.b = eval (mapAssignment codec api rho) row.b := by
    apply eval_agrees
    intro term present
    exact {inv}.preserves _ term.1 (map_outside row member term (List.mem_append_right _ present))
  rw [left,right]
  exact {whole}.complete_rows cardinality codec api rho one four linked row member
'''
    exports += ['map_outside', 'map_rows_complete']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
