"""Exact captured loop template transport with complete LC-valued images."""
from . import transfer_relation as relation, transfer_ownership as ownership
from . import transfer_linear_substitution as substitution


def unoutline(terms, copy):
    """Canonical compiler copy normalization; its actual link is checked below."""
    return ownership.canonical((0 if column == copy else column, factor)
                               for column, factor in terms)


def window_substitution(template, template_rows, target, target_rows,
                        template_offset=0, target_offset=0, *, include_precompute=False):
    """Retain genuine template/DH records and check every formula/compiler role."""
    for key in ('relation_digest', 'domain_size', 'full_rows', 'constant_copy'):
        if template['metadata'][key] != target['metadata'][key]:
            raise relation.RelationError('DH substitution exact relation/shape mismatch')
    if target['metadata'].get('schema') != 'shieldd-transfer-encryption-dh-v1' or target.get('qualified') is not True:
        raise relation.RelationError('DH substitution qualified genuine occurrence required')
    if type(template_offset) is not int or type(target_offset) is not int or type(include_precompute) is not bool:
        raise relation.RelationError('DH substitution offset/precompute types')
    if (not 0 <= template_offset < template['metadata']['window_count'] or
            not 0 <= target_offset < target['metadata']['window_count']):
        raise relation.RelationError('DH substitution window offset outside capture')
    positions = (template['metadata']['window_start'] + template_offset,
                 target['metadata']['window_start'] + target_offset)
    if min(positions) <= 0 and not (positions == (0, 0) and include_precompute):
        raise relation.RelationError('DH substitution initial window requires paired precompute')
    t_cones = ownership.cone_certificates(template, template_rows, template_offset, include_precompute)
    a_cones = ownership.cone_certificates(target, target_rows, target_offset, include_precompute)
    t_quotients = ownership.quotient_certificates(template, template_rows, template_offset, include_precompute)
    a_quotients = ownership.quotient_certificates(target, target_rows, target_offset, include_precompute)
    t_match = ownership.match_formulas(template)['cones'][8 + 14 * template_offset:22 + 14 * template_offset]
    a_match = ownership.match_formulas(target)['cones'][8 + 14 * target_offset:22 + 14 * target_offset]
    if include_precompute:
        t_match = ownership.match_formulas(template)['cones'][:8] + t_match
        a_match = ownership.match_formulas(target)['cones'][:8] + a_match
    if not (len(t_cones['cones']) == len(a_cones['cones']) == len(t_match) == len(a_match)):
        raise relation.RelationError('DH substitution exact cone count')
    lc_pairs, row_pairs = [], []
    for t_cone, a_cone, t_formula, a_formula in zip(t_cones['cones'], a_cones['cones'], t_match, a_match):
        if t_formula['graph'] != a_formula['graph']:
            raise relation.RelationError('DH substitution independent formula mismatch')
        t_pairs, a_pairs = dict(t_formula['pairs']), dict(a_formula['pairs'])
        if set(t_pairs) != set(a_pairs) or len(t_cone['inputs']) != len(a_cone['inputs']):
            raise relation.RelationError('DH substitution exact source correspondence')
        for identity in sorted(t_pairs):
            t_name, a_name = t_pairs[identity], a_pairs[identity]
            lc_pairs.append((t_cones['observations'][t_name][1], a_cones['observations'][a_name][1]))
            t_certificate, a_certificate = t_cone['certificates'][t_name], a_cone['certificates'][a_name]
            if (t_certificate['kind'] != a_certificate['kind'] or
                    len(t_certificate.get('rows', [])) != len(a_certificate.get('rows', []))):
                raise relation.RelationError('DH substitution compiler-case mismatch')
            row_pairs.extend(zip(t_certificate.get('rows', []), a_certificate.get('rows', [])))
        for t_name, a_name in zip(t_cone['inputs'], a_cone['inputs']):
            lc_pairs.append((t_cones['observations'][t_name][1], a_cones['observations'][a_name][1]))
    if len(t_quotients['certificates']) != len(a_quotients['certificates']):
        raise relation.RelationError('DH substitution exact quotient count')
    for t_certificate, a_certificate in zip(t_quotients['certificates'], a_quotients['certificates']):
        if t_certificate['kind'] != a_certificate['kind'] or len(t_certificate['rows']) != len(a_certificate['rows']):
            raise relation.RelationError('DH substitution quotient-case mismatch')
        lc_pairs.extend((t_certificate[role], a_certificate[role]) for role in ('numerator', 'denominator', 'quotient', 'output'))
        row_pairs.extend(zip(t_certificate['rows'], a_certificate['rows']))
    t_rows = {**t_cones['rows'], **t_quotients['rows']}
    a_rows = {**a_cones['rows'], **a_quotients['rows']}
    t_link = (ownership.canonical([(0, 1), (t_cones['outline'], -1)]), ())
    a_link = (ownership.canonical([(0, 1), (a_cones['outline'], -1)]), ())
    t_links = [index for index, row in t_rows.items() if row == t_link]
    a_links = [index for index, row in a_rows.items() if row == a_link]
    if len(t_links) != 1 or len(a_links) != 1:
        raise relation.RelationError('DH substitution exact constant-copy assertion')
    row_pairs.append((t_links[0], a_links[0]))
    lc_pairs.extend((left, right) for original, actual in row_pairs for left, right in zip(t_rows[original], a_rows[actual]))
    # Observer LCs use zero for the constant, while emitted compiler LCs can
    # use the outlined private copy. The two exact physical link assertions
    # above are required before treating these expressions as equal. Generated
    # kernels retain raw physical rows and derive normalized satisfaction with
    # Compiler.unoutline_rows_sound; normalization is not a proof by itself.
    normalized_t_rows = {i: tuple(unoutline(side, t_cones['outline']) for side in row)
                         for i, row in t_rows.items()}
    normalized_a_rows = {i: tuple(unoutline(side, a_cones['outline']) for side in row)
                         for i, row in a_rows.items()}
    normalized_pairs = [(unoutline(left, t_cones['outline']), unoutline(right, a_cones['outline']))
                        for left, right in lc_pairs]
    selected = substitution.infer(normalized_pairs, row_pairs, normalized_t_rows, normalized_a_rows,
                                  source_copy=t_cones['outline'], actual_copy=a_cones['outline'])
    columns = dict(selected['columns'])
    # This entry was unused in the normalized inference. The original source
    # copy now reads zero's LC, so the source link transports to a zero row.
    columns[t_cones['outline']] = ((0, 1),)
    selected.update(columns=sorted(columns.items()), source_rows=t_rows, actual_rows=a_rows,
                    actual_copy=a_cones['outline'], unoutlined=True)
    selected.update(template_offset=template_offset, target_offset=target_offset,
                    scope='Exact captured formula/compiler/LC/row substitution only; kernel roles/satisfaction/full loop/native/caller transport OPEN')
    return selected


def chunk_substitution(template, template_rows, target, target_rows):
    """Merge at most16 checked windows and their exact original Boolean rows."""
    t_metadata, a_metadata = template['metadata'], target['metadata']
    if (t_metadata['window_start'], t_metadata['window_count']) != (a_metadata['window_start'], a_metadata['window_count']):
        raise relation.RelationError('DH substitution exact chunk interval')
    count = t_metadata['window_count']
    if type(count) is not int or not 1 <= count <= 16:
        raise relation.RelationError('DH substitution bounded16-window chunk')
    columns, windows = {}, []
    source_rows, actual_rows, row_targets = {}, {}, {}
    for offset in range(count):
        selected = window_substitution(template, template_rows, target, target_rows, offset, offset,
                                       include_precompute=t_metadata['window_start'] + offset == 0)
        for source, terms in selected['columns']:
            if source in columns and columns[source] != terms:
                raise relation.RelationError('DH substitution cross-window LC image disagreement')
            columns[source] = terms
        for destination, incoming in ((source_rows, selected['source_rows']), (actual_rows, selected['actual_rows'])):
            for index, row in incoming.items():
                if index in destination and destination[index] != row:
                    raise relation.RelationError('DH substitution cross-window physical-row disagreement')
                destination[index] = row
        for source, actual in selected['row_targets']:
            if source in row_targets and row_targets[source] != actual:
                raise relation.RelationError('DH substitution cross-window row-target disagreement')
            row_targets[source] = actual
        windows.append(selected)

    def boolean_rows(extracted):
        result = {}
        for item in extracted['templates']:
            for role in item['roles']:
                if role.startswith('bit.'):
                    if role in result and result[role] != item['row']:
                        raise relation.RelationError('DH substitution duplicated bit row role')
                    result[role] = item['row']
        return result

    t_bits, a_bits = boolean_rows(template_rows), boolean_rows(target_rows)

    def physical(extracted):
        return {row['row']: tuple(tuple((column, int(value, 16)) for column, value in row[side])
                                 for side in ('a', 'b')) for row in extracted['selected_rows']}

    t_physical, a_physical = physical(template_rows), physical(target_rows)
    low = 2 * (126 - t_metadata['window_start'] - count)
    high = 2 * (126 - t_metadata['window_start'])
    for index in range(low, high):
        role = 'bit.' + str(index)
        if role not in t_bits or role not in a_bits:
            raise relation.RelationError('DH substitution original Boolean row missing')
        t_terms = template['derived'][template['bits'][index]]
        a_terms = target['derived'][target['bits'][index]]
        if substitution.linear(t_terms, columns) != a_terms:
            raise relation.RelationError('DH substitution exact decoded bit role mismatch')
        original, actual = t_bits[role], a_bits[role]
        if original not in t_physical or actual not in a_physical:
            raise relation.RelationError('DH substitution original Boolean physical row missing')
        renamed = tuple(substitution.linear(terms, columns) for terms in t_physical[original])
        wanted = tuple(unoutline(side, target['metadata']['constant_copy']) for side in a_physical[actual])
        if renamed not in (wanted, (ownership.canonical((column, -factor) for column, factor in wanted[0]), wanted[1])):
            raise relation.RelationError('DH substitution original Boolean row mismatch')
        if original in row_targets and row_targets[original] != actual:
            raise relation.RelationError('DH substitution Boolean row-target disagreement')
        source_rows[original], actual_rows[actual], row_targets[original] = t_physical[original], a_physical[actual], actual
    return dict(columns=sorted(columns.items()), windows=windows, source_rows=source_rows, actual_rows=actual_rows,
                row_targets=sorted(row_targets.items()), actual_copy=a_metadata['constant_copy'], unoutlined=True,
                scope='Exact bounded chunk LC/window/Boolean-row substitution only; kernel/common126-loop/native/caller transport OPEN')


def merge_substitutions(chunks):
    """Retain a single assignment substitution and every original row target.

    Local checks alone are insufficient: a column shared by adjacent windows
    must have the same image throughout the complete loop.
    """
    if not isinstance(chunks, list) or len(chunks) != 8:
        raise relation.RelationError('DH substitution exactly eight checked chunks')
    columns, source_rows, actual_rows, targets = {}, {}, {}, {}
    copies = {chunk.get('actual_copy') for chunk in chunks}
    if len(copies) != 1 or any(chunk.get('unoutlined') is not True for chunk in chunks):
        raise relation.RelationError('DH substitution common checked copy normalization')
    actual_copy = copies.pop()
    if type(actual_copy) is not int or not 3 <= actual_copy < 2**32:
        raise relation.RelationError('DH substitution actual copy column')
    for chunk in chunks:
        entries = chunk['columns']
        if len(entries) != len(dict(entries)):
            raise relation.RelationError('DH substitution duplicate source column image')
        incoming_targets = chunk['row_targets']
        if len(incoming_targets) != len(dict(incoming_targets)):
            raise relation.RelationError('DH substitution duplicate original row target')
        for accumulated, incoming in ((columns, dict(entries)), (source_rows, chunk['source_rows']),
                                      (actual_rows, chunk['actual_rows']), (targets, dict(incoming_targets))):
            for identity, value in incoming.items():
                if identity in accumulated and accumulated[identity] != value:
                    raise relation.RelationError('DH substitution common-assignment image/row disagreement')
                accumulated[identity] = value
        if len(columns) > 65536 or len(source_rows) > 65536 or len(actual_rows) > 65536:
            raise relation.RelationError('DH substitution full-loop finite support bound')
    if set(targets) != set(source_rows):
        raise relation.RelationError('DH substitution full-loop original-row coverage')
    if columns.get(0) != ((0, 1),):
        raise relation.RelationError('DH substitution full-loop constant-one image')
    for original, actual in targets.items():
        if actual not in actual_rows:
            raise relation.RelationError('DH substitution full-loop actual row missing')
        renamed = tuple(substitution.linear(terms, columns) for terms in source_rows[original])
        wanted = tuple(unoutline(side, actual_copy) for side in actual_rows[actual])
        reversed_input = (ownership.canonical((column, -factor) for column, factor in wanted[0]), wanted[1])
        if renamed not in (wanted, reversed_input):
            raise relation.RelationError('DH substitution full-loop actual row mismatch')
    return dict(columns=sorted(columns.items()), source_rows=source_rows, actual_rows=actual_rows,
                row_targets=sorted(targets.items()), chunks=chunks, actual_copy=actual_copy, unoutlined=True,
                scope='One exact common-assignment LC/row substitution; kernel/full-loop/native/caller transport OPEN')


def full_substitution(template_chunks, template_rows, target_chunks, target_rows):
    """Transport genuine owned loop templates to one encryption occurrence.

    Keep the original ownership or RNK schema. Select only the multiplication
    cones, quotient and bit rows; exclude ownership endpoint assertions and RNK
    nonidentity/hash/action-key assertions. Kernel composition must use the
    multiplication theorem that derives its endpoint from those loop rows.
    """
    from . import transfer_encryption_dh as dh
    if any(not isinstance(items, list) or len(items) != 8
           for items in (template_chunks, template_rows, target_chunks, target_rows)):
        raise relation.RelationError('DH substitution full eight-page collections')
    schemas = {chunk['metadata'].get('schema') for chunk in template_chunks}
    if len(schemas) != 1 or not schemas <= {'shieldd-transfer-ownership-v1', 'shieldd-transfer-rnk-dh-v1'}:
        raise relation.RelationError('DH substitution genuine uniform owned multiplication template required')
    ownership.join_chunks(template_chunks)
    target = dh.inspect_chunks(target_chunks)
    if target['qualified'] is not True:
        raise relation.RelationError('DH substitution qualified complete occurrence required')
    chunks = [chunk_substitution(source, source_rows, actual, actual_rows)
              for source, source_rows, actual, actual_rows
              in zip(template_chunks, template_rows, target_chunks, target_rows)]
    combined = merge_substitutions(chunks)
    columns = dict(combined['columns'])

    def terms(checked, value):
        return checked['derived'][value[1]] if value[0] == 'source' else ownership.canonical([(0, value[1])])

    roles = {}
    for name in ('base', 'twice', 'triple', 'output'):
        source = tuple(terms(template_chunks[0], value) for value in template_chunks[0]['points'][name])
        actual = tuple(terms(target_chunks[0], value) for value in target_chunks[0]['points'][name])
        if tuple(substitution.linear(value, columns) for value in source) != actual:
            raise relation.RelationError('DH substitution full-loop exact point role mismatch')
        roles[name] = dict(source=source, actual=actual)
    source_bits = [template_chunks[0]['derived'][handle] for handle in template_chunks[0]['bits']]
    actual_bits = [target_chunks[0]['derived'][handle] for handle in target_chunks[0]['bits']]
    if len(source_bits) != 252 or len(actual_bits) != 252 or [substitution.linear(bit, columns) for bit in source_bits] != actual_bits:
        raise relation.RelationError('DH substitution full-loop exact252 bit roles')
    roles['bits'] = dict(source=source_bits, actual=actual_bits)
    # Existing RuntimeRnkTrace modules use an explicitly checked arithmetic
    # renaming of the genuine ownership templates. Reuse that exact candidate
    # only as a source-column view; generated kernel checks must still compare
    # every original RuntimeRnkTrace row and every endpoint/bit expression.
    rename = ownership.rnk_column_candidate if schemas == {'shieldd-transfer-ownership-v1'} else lambda column: column
    loop_columns = {}
    for column, value in combined['columns']:
        image = rename(column)
        if image in loop_columns and loop_columns[image] != value:
            raise relation.RelationError('DH substitution reused RNK template column collision')
        loop_columns[image] = value
    loop_roles = {name: dict(source=[ownership.canonical((rename(column), factor) for column, factor in terms)
                                    for terms in role['source']], actual=role['actual'])
                  for name, role in roles.items()}
    combined.update(roles=roles, windows=126, role=target['role'], qualified=True,
                    template_schema=next(iter(schemas)), loop_columns=sorted(loop_columns.items()), loop_roles=loop_roles,
                    scope='Genuine complete126-window owned-loop-to-DH LC/row/point/252-bit correspondence; kernel/full-loop/native/caller transport OPEN')
    return combined
