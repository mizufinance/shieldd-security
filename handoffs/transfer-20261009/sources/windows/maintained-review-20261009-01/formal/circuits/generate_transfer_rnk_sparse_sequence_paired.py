"""Linear checked row-pair certificates for the unchanged RNK constructors.

The strict sparse parser supplies physical source/target row identities. Lean
checks each selected pair and proves source membership separately; it never
searches a Cartesian product of canonical field equations.
"""
import re
from . import generate_transfer_rnk_sparse_sequence as base
from . import transfer_ownership_completion as owned
from . import transfer_rnk_completion as sparse


def _paired(source, source_rows, target_rows, plan, columns):
    by_index = {row['row']: row for row in source_rows}
    assert [row['row'] for row in target_rows] == plan['target_rows']
    chosen = [item['source_rows'][0] for item in plan['coverage']]
    assert len(chosen) == len(target_rows)
    positions = [plan['source_rows'].index(index) for index in chosen]
    covered = [by_index[index] for index in chosen]
    relation = (
        'Compiler.canonical Scalar.modulus (RowRenaming.linear '+columns+' original.a) = '
        'Compiler.canonical Scalar.modulus actual.a ∧\n'
        '    Compiler.canonical Scalar.modulus (RowRenaming.linear '+columns+' original.b) = '
        'Compiler.canonical Scalar.modulus actual.b')
    marker = re.search(r'^(private )?theorem row_coverage :', source, re.M)
    assert marker is not None
    ending = source.index('\n', source.index('  exact ⟨original,present,of_decide_eq_true equal⟩', marker.start()))
    old = source[marker.start():ending]
    assert 'sourceRows.any' in old
    membership = '''private def coverageSources : List Row := '''+base._row_literal(covered)+'''
private theorem coverage_sources : ∀ original ∈ coverageSources, original ∈ sourceRows := by
  intro original member
  simp only [coverageSources, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in covered)+'\n'
    membership += ''.join('  · exact '+base._list_member(position)+'\n' for position in positions)
    replacement = membership+(marker.group(1) or '')+'theorem row_coverage : ∀ actual ∈ actualRows, ∃ original ∈ sourceRows,\n    '+relation+''' := by
  have checked : RowPairedCoverage.check (fun original actual => decide
    ('''+relation+''')) coverageSources actualRows = true := by decide
  intro actual member
  obtain ⟨original, present, equal⟩ := RowPairedCoverage.covered _ _ _ checked actual member
  exact ⟨original, coverage_sources original present, of_decide_eq_true equal⟩'''
    return 'import ShielddSecurity.RowPairedCoverage\n'+source[:marker.start()]+replacement+source[ending:]


def generate_blocks(plan):
    outputs = base.generate_blocks(plan)
    for index, (block, local) in enumerate(zip(plan['row_blocks'], plan['blocks'])):
        name = f'RuntimeRnkSparseBlock{index:03d}'
        outputs[name] = _paired(outputs[name], block['source_rows'], block['target_rows'],
                                local, 'GroupRnkSparseColumns.columns')
    return outputs


def generate_native_source(checked, selection, rnk, transport, reduction_plan, plan):
    name, source = base.generate_native_source(checked, selection, rnk, transport, reduction_plan, plan)
    local = owned.window_plan(checked, selection, 0, True)
    raw = {row['row']: row for row in selection['selected_rows']}
    source_rows = [raw[index] for index in local['local_rows']]
    target_rows = transport['chunks'][0]['blocks'][0]
    paired = sparse.sparse_transport_plan(source_rows, target_rows, local['writes'],
        domain_size=checked['metadata']['domain_size'], full_rows=checked['metadata']['full_rows'],
        protected_columns=plan['protected_columns'])
    return name, _paired(source, source_rows, target_rows, paired, 'columns')


generate_assignment = base.generate_assignment
generate_native_chunks = base.generate_native_chunks
generate_join = base.generate_join
