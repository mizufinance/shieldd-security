"""Finite sparse-write certificates for retained actual RNK loop rows.

Inputs are already accepted source/ordinary row selections. This helper checks
their complete side equations and a bounded write/support map; it neither
qualifies a capture nor supplies the completed source assignment. The caller
must derive that assignment from the maintained ownership constructor.
"""
from . import transfer_relation as relation, transfer_ownership as ownership
from .transfer_balance_rows import canonical


def _rows(values, domain, full_rows):
    if not isinstance(values, list) or not 0 < len(values) <= 512:
        raise relation.RelationError('RNK sparse bounded nonempty row block')
    result = {};previous = -1
    for value in values:
        if not isinstance(value, dict) or set(value) != {'row', 'a', 'b'}:
            raise relation.RelationError('RNK sparse exact physical row shape')
        index = relation.natural(value['row'], full_rows)
        if index <= previous:
            raise relation.RelationError('RNK sparse ordered distinct physical rows')
        previous = index
        for side in ('a', 'b'):
            relation.terms(value[side], domain)
        result[index] = tuple(tuple((column, int(coefficient, 16))
                                   for column, coefficient in value[side])
                              for side in ('a', 'b'))
    return result


def _columns(values, domain, label):
    if not isinstance(values, list) or len(values) > 4096:
        raise relation.RelationError('RNK sparse bounded '+label)
    checked = [relation.natural(column, domain) for column in values]
    if checked != sorted(set(checked)):
        raise relation.RelationError('RNK sparse canonical '+label)
    return checked


def sparse_transport_plan(source_rows, target_rows, source_writes, *,
                          domain_size, full_rows, protected_columns=()):
    """Check one actual row block and only its owned sparse target writes.

    Restricted injectivity applies to ``source_writes``. Every nonwritten row
    support must avoid their image. Source preservation on those supports is a
    separate conclusion of the earlier owned constructors, including earlier
    sparse chunks; it is never inferred from this structural certificate.
    """
    domain = relation.natural(domain_size, 2**32)
    count = relation.natural(full_rows, 2**64)
    if domain < 4 or domain & (domain-1) or not 0 < count <= domain:
        raise relation.RelationError('RNK sparse canonical relation shape')
    source = _rows(source_rows, domain, count)
    target = _rows(target_rows, domain, count)
    writes = _columns(source_writes, domain, 'source writes')
    if len(writes) > 512:
        raise relation.RelationError('RNK sparse bounded local writes')
    if not isinstance(protected_columns, (tuple, list)):
        raise relation.RelationError('RNK sparse typed protected columns')
    protected = _columns(list(protected_columns), domain, 'protected columns')
    support = sorted({column for sides in source.values()
                      for side in sides for column, _ in side})
    mapping = {column: ownership.rnk_column_candidate(column)
               for column in set(support) | set(writes)}
    for column in mapping.values():
        relation.natural(column, domain)
    images = [mapping[column] for column in writes]
    if len(set(images)) != len(images):
        raise relation.RelationError('RNK sparse owned write image collision')
    if set(images) & set(protected):
        raise relation.RelationError('RNK sparse writes overwrite protected target')
    if any(mapping[column] in images for column in set(support) - set(writes)):
        raise relation.RelationError('RNK sparse nonwritten support image alias')
    if not set(writes) <= set(support):
        raise relation.RelationError('RNK sparse writes require actual row support')
    mapped = {}
    for index, sides in source.items():
        key = tuple(canonical((mapping[column], coefficient)
                              for column, coefficient in side) for side in sides)
        mapped.setdefault(key, []).append(index)
    coverage = []
    target_keys = set()
    for index, sides in target.items():
        if sides not in mapped:
            raise relation.RelationError('RNK sparse exact actual side coverage')
        coverage.append({'target_row': index, 'source_rows': mapped[sides]})
        target_keys.add(sides)
    if set(mapped) != target_keys:
        raise relation.RelationError('RNK sparse missing transported source row')
    return {
        'schema': 'shieldd-transfer-rnk-sparse-plan-v1',
        'domain_size': domain, 'full_rows': count,
        'source_writes': writes, 'target_writes': images,
        'source_support': support,
        'nonwritten_support': sorted(set(support) - set(writes)),
        'column_pairs': [[column, mapping[column]] for column in sorted(mapping)],
        'protected_columns': protected, 'coverage': coverage,
        'source_rows': list(source), 'target_rows': list(target),
        'scope': 'finite actual row/write map only; source completion, native input, scalar, caller, and whole-row joins remain separate',
    }


def sparse_sequence_plan(blocks, *, domain_size, full_rows, protected_columns=()):
    """Check bounded blocks against one whole owned-write/support certificate.

    All blocks read the same completed source assignment. Shared physical rows
    may recur only with identical equations. Physical writes belong to exactly
    one block. Crucially, injectivity and nonwritten-support exclusion are
    checked again over the entire sequence, including cross-block aliases.
    This structural plan does not establish source row satisfaction or qualify
    the supplied retained selections.
    """
    if not isinstance(blocks, list) or not 0 < len(blocks) <= 256:
        raise relation.RelationError('RNK sparse bounded nonempty sequence')
    plans = []
    source_records = {}; target_records = {}; written = set()
    for block in blocks:
        if not isinstance(block, dict) or set(block) != {
                'source_rows', 'target_rows', 'source_writes'}:
            raise relation.RelationError('RNK sparse exact sequence block shape')
        plan = sparse_transport_plan(**block, domain_size=domain_size,
            full_rows=full_rows, protected_columns=protected_columns)
        current = set(plan['source_writes'])
        if written & current:
            raise relation.RelationError('RNK sparse repeated physical write ownership')
        written.update(current)
        for label, records in (('source_rows', source_records),
                               ('target_rows', target_records)):
            for record in block[label]:
                index = record['row']
                if index in records and records[index] != record:
                    raise relation.RelationError('RNK sparse conflicting shared physical row')
                records[index] = record
        if max(len(written), len(source_records), len(target_records)) > 8192:
            raise relation.RelationError('RNK sparse bounded whole sequence')
        plans.append(plan)
    support = sorted({column for plan in plans for column in plan['source_support']})
    if len(support) > 8192:
        raise relation.RelationError('RNK sparse bounded whole support')
    writes = sorted(written)
    mapping = {column: ownership.rnk_column_candidate(column) for column in support}
    images = [mapping[column] for column in writes]
    if len(set(images)) != len(images):
        raise relation.RelationError('RNK sparse whole write image collision')
    image_set = set(images)
    if any(mapping[column] in image_set for column in set(support) - written):
        raise relation.RelationError('RNK sparse whole nonwritten support image alias')
    return {
        'schema': 'shieldd-transfer-rnk-sparse-sequence-plan-v1',
        'domain_size': plans[0]['domain_size'], 'full_rows': plans[0]['full_rows'],
        'blocks': plans, 'source_writes': writes, 'target_writes': images,
        'source_support': support, 'nonwritten_support': sorted(set(support) - written),
        'column_pairs': [[column, mapping[column]] for column in support],
        'protected_columns': plans[0]['protected_columns'],
        'source_rows': sorted(source_records), 'target_rows': sorted(target_records),
        'scope': 'whole restricted write/support checks and bounded exact row coverage only; one owned source constructor, shared consumer preservation, native and caller joins remain separate',
    }


def ownership_sequence_plan(chunks, selections, transport, rnk_prefix, *, protected_columns=()):
    """Bind all126 owned local recipes to the retained actual RNK row maps.

    ``chunks`` and ``rnk_prefix`` are accepted parser results; ``selections``
    and ``transport`` are retained exact ordinary-row selections. No stream is
    opened. The four actual RNK source captures establish observed common
    base/output/bit operands; rows for the remaining windows are supplied by
    the accepted original-row transport, without synthesizing source handles.
    Every window and each chunk's Boolean bit rows remain a <=512-row block.
    """
    try:
        return _ownership_sequence_plan(chunks, selections, transport, rnk_prefix,
                                        protected_columns=protected_columns)
    except (KeyError, TypeError, IndexError, AttributeError) as error:
        raise relation.RelationError('RNK sparse typed accepted sequence inputs') from error


def _ownership_sequence_plan(chunks, selections, transport, rnk_prefix, *, protected_columns):
    from . import transfer_ownership_completion as owned
    layout = [(start, min(16, 126-start)) for start in range(0, 126, 16)]
    if not isinstance(chunks, list) or not isinstance(selections, list) or \
            len(chunks) != 8 or len(selections) != 8:
        raise relation.RelationError('RNK sparse eight accepted owner chunks/selections')
    ownership.join_chunks(chunks)
    if [(value['metadata']['window_start'], value['metadata']['window_count'])
            for value in chunks] != layout or any(value['metadata']['schema'] !=
            'shieldd-transfer-ownership-v1' for value in chunks):
        raise relation.RelationError('RNK sparse canonical accepted owner intervals')
    if not isinstance(rnk_prefix, list) or len(rnk_prefix) != 4 or \
            [(value['metadata']['window_start'], value['metadata']['window_count'])
             for value in rnk_prefix] != layout[:4]:
        raise relation.RelationError('RNK sparse four accepted observed RNK intervals')
    if [(value['start'], value['count']) for value in transport['chunks']] != layout:
        raise relation.RelationError('RNK sparse all126 retained target intervals')
    metadata = chunks[0]['metadata']; identity = transport['identity']
    def same_identity(value):
        if any(value[key] != metadata[other] for key, other in (
                ('relation_digest', 'relation_digest'), ('domain_size', 'domain_size'),
                ('stored_rows', 'full_rows'))):
            raise relation.RelationError('RNK sparse exact common original relation')
    same_identity(identity)
    def point(checked, role):
        return [checked['derived'][value[1]] if value[0] == 'source' else
                canonical([(0, value[1])]) for value in checked['points'][role]]
    bits = [chunks[0]['derived'][handle] for handle in chunks[0]['bits']]
    if len(bits) != 252 or any(len(lc) != 1 or lc[0][1] != 1 for lc in bits):
        raise relation.RelationError('RNK sparse exact252 singleton scalar operands')
    bit_start = bits[0][0][0]
    if bits != [((bit_start+index, 1),) for index in range(252)]:
        raise relation.RelationError('RNK sparse contiguous source scalar operands')
    first_rnk = rnk_prefix[0]
    previous = None; expressions = {}; nodes = {}
    for accepted in rnk_prefix:
        m = accepted['metadata']
        if m['schema'] != 'shieldd-transfer-rnk-dh-v1' or any(m[key] != metadata[key]
                for key in ('relation_digest', 'domain_size', 'full_rows', 'constant_copy',
                            'ivk_handles', 'remainder', 'remainder_bits', 'bits')):
            raise relation.RelationError('RNK sparse same accepted IVK/scalar/shape roles')
        if any(m[key] != first_rnk['metadata'][key] for key in
               ('base', 'twice', 'triple', 'output', 'nonidentity_inverse', 'rnk_bindings')):
            raise relation.RelationError('RNK sparse consistent observed native/boundary roles')
        for role in ('base', 'twice', 'triple', 'output'):
            mapped = [canonical((ownership.rnk_column_candidate(c), v) for c, v in lc)
                      for lc in point(chunks[0], role)]
            if mapped != point(accepted, role):
                raise relation.RelationError('RNK sparse observed common point LC map')
        if previous is not None and accepted['windows'][0][0] != previous:
            raise relation.RelationError('RNK sparse observed chunk point continuity')
        previous = accepted['windows'][-1][4]
        for collection, observed in ((expressions, accepted['expressions']),
                                     (nodes, accepted['nodes'])):
            for handle, value in observed.items():
                if handle in collection and collection[handle] != value:
                    raise relation.RelationError('RNK sparse shared observed source identity/LC')
                collection[handle] = value
    row_blocks = []; roles = []
    for checked, selection, target in zip(chunks, selections, transport['chunks']):
        same_identity(selection['identity'])
        start = target['start']; count = target['count']
        if len(target['blocks']) != count+1:
            raise relation.RelationError('RNK sparse exact retained row block count')
        raw = {row['row']: row for row in selection['selected_rows']}
        if len(raw) != len(selection['selected_rows']):
            raise relation.RelationError('RNK sparse duplicate selected original row')
        for offset in range(count):
            local = owned.window_plan(checked, selection, offset, start+offset == 0)
            row_blocks.append(dict(source_rows=[raw[index] for index in local['local_rows']],
                target_rows=target['blocks'][offset], source_writes=local['writes']))
            roles.append(dict(kind='window', window=start+offset, chunk=start))
        bit_roles = {}
        for template in selection['templates']:
            for role in template['roles']:
                if role.startswith('bit.'):
                    if role in bit_roles:
                        raise relation.RelationError('RNK sparse duplicate actual Boolean role')
                    bit_roles[role] = template['row']
        bit_indices = range(2*(126-start-count), 2*(126-start))
        bit_rows = sorted({bit_roles['bit.'+str(index)] for index in bit_indices})
        if len(bit_rows) != 2*count:
            raise relation.RelationError('RNK sparse distinct actual Boolean bit rows')
        for index in bit_indices:
            lc = checked['derived'][checked['bits'][index]]
            parsed = _rows([raw[bit_roles['bit.'+str(index)]]], metadata['domain_size'], metadata['full_rows'])
            if next(iter(parsed.values())) != (lc, lc) or any(
                    ownership.rnk_column_candidate(c) != c for c, _ in lc):
                raise relation.RelationError('RNK sparse exact unchanged actual Boolean equation')
        row_blocks.append(dict(source_rows=[raw[index] for index in bit_rows],
            target_rows=target['blocks'][-1], source_writes=[]))
        roles.append(dict(kind='bits', chunk=start, bit_start=2*(126-start-count), width=2*count))
    result = sparse_sequence_plan(row_blocks, domain_size=metadata['domain_size'],
        full_rows=metadata['full_rows'], protected_columns=protected_columns)
    result.update(schema='shieldd-transfer-rnk-all126-sparse-plan-v1', identity=identity,
        windows=126, roles=roles, row_blocks=row_blocks,
        bit_start=bit_start, bit_width=252,
        observed_prefix_windows=64, observed_base=point(first_rnk, 'base'),
        observed_output=point(first_rnk, 'output'),
        observed_base_handles=first_rnk['metadata']['base'],
        observed_output_handles=first_rnk['metadata']['output'])
    return result
