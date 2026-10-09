"""Fail-closed structural compiler-completion selection for the full relation.

This is a source helper, not a second CLI. Its complete ordered row input must
come from the independently reconstructed full stream. E9's selected 8636 rows
and the eighteen-column support projection are insufficient. No actual full
lowering program has been exported/qualified, and this helper is not run here.
The source-node/algorithm/assertion meaning join is explicitly separate.
"""
from hash_rows import canonical, scaled

STORED_ROWS = 200770
CONSTANT_COPY = 200692
FIXED_INPUT_COLUMNS = frozenset((0, 1, 2, CONSTANT_COPY))


def _linear(value):
    if not isinstance(value, (list, tuple)):
        raise ValueError('linear terms required')
    terms = []
    for term in value:
        if not isinstance(term, (list, tuple)) or len(term) != 2:
            raise ValueError('complete linear term required')
        column, coefficient = term
        if type(column) is not int or not 0 <= column < 262144 or type(coefficient) is not int:
            raise ValueError('original column and integer coefficient required')
        terms.append((column, coefficient))
    return canonical(tuple(terms))


def _column(value):
    if type(value) is not int or not 0 <= value < 262144:
        raise ValueError('original column required')
    return value


def _step(step):
    common = {'kind', 'source_kind', 'source_id', 'row_indices'}
    if not isinstance(step, dict) or type(step.get('source_id')) is not int or step['source_id'] < 0:
        raise ValueError('explicit lowering source identity required')
    kind = step.get('kind')
    fields = {'square': {'input', 'remainder', 'output'},
        'product': {'left', 'right', 'remainder', 'output', 'auxiliary'},
        'equal': {'left', 'right'}, 'squareEqual': {'input', 'target'}}
    if kind not in fields or set(step) != common | fields[kind]:
        raise ValueError('unsupported/extra lowering fields; no omitted branch fallback')
    if step['source_kind'] != ('node' if kind in ('square', 'product') else 'assertion'):
        raise ValueError('node/assertion source identity namespaces must be explicit')
    terms = {name: _linear(step[name]) for name in fields[kind] if name not in ('output', 'auxiliary')}
    if kind == 'square':
        output = _column(step['output']); writes = [output]
        expected = [(terms['input'], canonical(((output, 1),) + terms['remainder']))]
        reads = terms['input'] + terms['remainder']
    elif kind == 'product':
        output, auxiliary = _column(step['output']), _column(step['auxiliary'])
        if output == auxiliary:
            raise ValueError('aliased product pivot/auxiliary')
        writes = [output, auxiliary]
        expected = [(canonical(terms['left'] + scaled(terms['right'], -1)), ((auxiliary, 1),)),
            (canonical(terms['left'] + terms['right']), canonical(((auxiliary, 1),) +
                scaled(((output, 1),) + terms['remainder'], 4)))]
        reads = terms['left'] + terms['right'] + terms['remainder']
    elif kind == 'equal':
        writes = []; reads = terms['left'] + terms['right']
        expected = [(canonical(terms['left'] + scaled(terms['right'], -1)), ())]
    else:
        writes = []; reads = terms['input'] + terms['target']
        expected = [(terms['input'], terms['target'])]
    if set(writes) & {column for column, _ in reads}:
        raise ValueError('materialized pivot occurs in its own operands/remainder')
    indices = step['row_indices']
    if not isinstance(indices, list) or len(indices) != len(expected) or any(type(i) is not int for i in indices):
        raise ValueError('exact original rows for every emitted constructor required')
    normalized = {**step, **terms, 'row_indices': list(indices)}
    return expected, writes, reads, normalized


def select(full_rows, lowering, kept, copy):
    """All-row coverage and no forward consumer/write, with original order retained.

    The generated structural data will need a kernel certificate, preferably
    indexed per block and composed symbolically. This Python selection alone is
    not the Topological/coverage theorem premise and proves no legal assertions.
    """
    if not isinstance(full_rows, list) or len(full_rows) != STORED_ROWS:
        raise ValueError('complete original 200770-row input required, never a selected slice')
    copy = _column(copy)
    if copy != CONSTANT_COPY:
        raise ValueError('pinned Transfer constant-copy column 200692 required')
    kept = [_column(column) for column in kept]
    if len(set(kept)) != len(kept) or not FIXED_INPUT_COLUMNS.issubset(kept):
        raise ValueError('distinct preserved constant/public/committed/copy columns required')
    actual = []
    for index, row in enumerate(full_rows):
        if not isinstance(row, dict) or set(row) != {'index', 'a', 'b'} or type(row['index']) is not int or row['index'] != index:
            raise ValueError('complete original index/order/body required')
        # Reuse the proved Compiler.unoutline transport; retain original bodies.
        normalized = []
        for side in ('a', 'b'):
            normalized.append(canonical(tuple((0 if column == copy else column, coefficient)
                for column, coefficient in _linear(row[side]))))
        actual.append(tuple(normalized))
    assigned, prior_support, covered, selected = set(), set(), set(), []
    source_ids = set()
    for stage, step in enumerate(lowering):
        expected, writes, reads, normalized_step = _step(step)
        identity = (step['source_kind'], step['source_id'])
        if identity in source_ids:
            raise ValueError('duplicate lowering source identity')
        source_ids.add(identity)
        if set(writes) & (set(kept) | assigned | prior_support):
            raise ValueError('later assignment overwrites fixed/prior-written/prior-consumed column')
        for index, body in zip(step['row_indices'], expected):
            if not 0 <= index < len(actual) or index in covered or actual[index] != body:
                raise ValueError('missing/aliased/changed original compiler row')
            covered.add(index)

        # Step.rows uses the normalized operands but may retain cancellation
        # between distinct operands. Structural preservation must retain every
        # term in those exact emitted constructors, not only canonical row support.
        prior_support.update(column for column, _ in reads)
        prior_support.update(writes)
        assigned.update(writes)
        selected.append({'stage': stage, 'step': normalized_step, 'writes': writes,
            'read_columns': sorted({column for column, _ in reads}), 'expected_rows': expected})
    if covered != set(range(STORED_ROWS)):
        raise ValueError('not every original row is completed exactly once')
    return {'steps': selected, 'original_rows': full_rows, 'kept': kept, 'copy': copy,
        'coverage_count': len(covered), 'assertion_semantics': 'independent algorithm/legal-input derivation still required',
        'kernel_boundary': 'exact full row data, structural topological certificate, and canonical coverage not qualified by Python'}
