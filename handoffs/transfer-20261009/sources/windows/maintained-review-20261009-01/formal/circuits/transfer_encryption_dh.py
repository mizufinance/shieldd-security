"""Closed bounded ingress for the five encryption variable-base occurrences.

Source/LC checks and ordinary replay qualification do not establish division,
curve membership, scalar interpretation, key selection, or multiplication.
The checked structure can feed the existing owned variable-loop row checker.
"""
import hashlib
import re
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index

SCOPE = 'bounded exact encryption DH occurrence; source/row/group/caller joins open'
IDENTITY = ('relation_digest', 'domain_size', 'full_rows', 'constant_copy')


def inspect_source_metadata(data, expected_relation, expected_role):
    """Parse pending observer bytes, retaining both FALSE qualification flags."""
    return _inspect(data, expected_relation, expected_role, False)


def inspect_qualified_metadata(data, expected_relation, expected_role):
    """Parse the actual four-spool qualifier's output; no kernel credit."""
    return _inspect(data, expected_relation, expected_role, True)


def _inspect(data, expected_relation, expected_role, qualified):
    if not isinstance(expected_relation, str) or not re.fullmatch('[0-9a-f]{64}', expected_relation):
        raise relation.RelationError('DH exact relation digest required')
    if type(expected_role) is not int or not 0 <= expected_role < 5:
        raise relation.RelationError('DH exact occurrence outside five roles')
    if not isinstance(data, bytes) or not 0 < len(data) <= 2 * 1024 * 1024:
        raise relation.RelationError('DH metadata 2MiB bound')
    obj = relation.record(data)
    keys = {'schema', 'family', 'scope', *IDENTITY, 'role', 'scalar', 'flagged',
            'detection_key', 'payload_key', 'window_start', 'window_count',
            'total_windows', 'base', 'twice', 'triple', 'bits', 'output',
            'windows', 'window_bits', 'quotients', 'expressions', 'nodes',
            'ordinary_full_ordered_rows_equal', 'repeated_observations_equal'}
    if (set(obj) != keys or obj['schema'] != 'shieldd-transfer-encryption-dh-v1' or
            obj['family'] != 'transfer' or obj['scope'] != SCOPE or
            type(obj['role']) is not int or obj['role'] != expected_role):
        raise relation.RelationError('DH closed schema/occurrence mismatch')
    if obj['relation_digest'] != expected_relation:
        raise relation.RelationError('DH relation identity mismatch')
    if any(obj[key] is not qualified for key in
           ('ordinary_full_ordered_rows_equal', 'repeated_observations_equal')):
        raise relation.RelationError('DH ordinary/repeated qualification mismatch')
    domain = relation.natural(obj['domain_size'])
    full_rows = relation.natural(obj['full_rows'])
    copy = relation.natural(obj['constant_copy'], domain)
    if domain < 4 or domain & (domain - 1) or not 0 < full_rows <= domain or copy < 3:
        raise relation.RelationError('DH relation bounds')
    start = relation.natural(obj['window_start'], 126)
    count = relation.natural(obj['window_count'], 17)
    if (not 1 <= count <= 16 or start + count > 126 or
            type(obj['total_windows']) is not int or obj['total_windows'] != 126):
        raise relation.RelationError('DH bounded window interval')
    roots = set()

    def observed(value):
        if isinstance(value, dict) and set(value) == {'source'}:
            handle = source_index(value['source'])
            if handle[0] == 1 and handle[1] + 3 >= domain:
                raise relation.RelationError('DH source outside domain')
            roots.add(handle)
            return ('source', handle)
        if (isinstance(value, dict) and set(value) == {'native'} and
                isinstance(value['native'], str) and re.fullmatch('[0-9a-f]{64}', value['native'])):
            number = int(value['native'], 16)
            if number < relation.MODULUS:
                return ('native', number)
        raise relation.RelationError('DH noncanonical observed value')

    def pair(values):
        if not isinstance(values, list) or len(values) != 2:
            raise relation.RelationError('DH point arity')
        return tuple(observed(value) for value in values)

    def handles(values, length):
        if not isinstance(values, list) or len(values) != length:
            raise relation.RelationError('DH bit arity')
        result = tuple(source_index(value) for value in values)
        if any(tag != 1 or index + 3 >= domain for tag, index in result):
            raise relation.RelationError('DH bits must be bounded witness handles')
        return result

    bits = handles(obj['bits'], 252)
    if len(set(bits)) != 252:
        raise relation.RelationError('DH duplicate bit handle')
    roots.update(bits)
    bindings = {'scalar': observed(obj['scalar']), 'flagged': observed(obj['flagged']),
                'detection_key': pair(obj['detection_key']), 'payload_key': pair(obj['payload_key'])}
    if bindings['scalar'][0] != 'source' or bindings['scalar'][1][0] != 1:
        raise relation.RelationError('DH scalar must be actual witness')
    points = {key: pair(obj[key]) for key in ('base', 'twice', 'triple', 'output')}
    if expected_role == 0 and points['base'] != bindings['detection_key']:
        raise relation.RelationError('DH unconditional detection base mismatch')
    if (not isinstance(obj['windows'], list) or len(obj['windows']) != count or
            not isinstance(obj['window_bits'], list) or len(obj['window_bits']) != count):
        raise relation.RelationError('DH window collection count')
    windows = []
    for offset, (window, window_bits) in enumerate(zip(obj['windows'], obj['window_bits'])):
        if not isinstance(window, list) or len(window) != 5:
            raise relation.RelationError('DH five-point window shape')
        low = 2 * (125 - start - offset)
        if handles(window_bits, 2) != bits[low:low + 2]:
            raise relation.RelationError('DH reversed bit order mismatch')
        parsed = tuple(pair(value) for value in window)
        if windows and parsed[0] != windows[-1][4]:
            raise relation.RelationError('DH accumulator chain mismatch')
        windows.append(parsed)
    if start == 0 and windows[0][0] != (('native', 0), ('native', 1)):
        raise relation.RelationError('DH initial accumulator must be identity')
    if start + count == 126 and windows[-1][4] != points['output']:
        raise relation.RelationError('DH final output association mismatch')
    if not isinstance(obj['quotients'], list) or len(obj['quotients']) != 2 + 3 * count:
        raise relation.RelationError('DH quotient count')
    quotients = []
    for values in obj['quotients']:
        if not isinstance(values, list) or len(values) != 6:
            raise relation.RelationError('DH quotient tuple arity')
        quotients.append(tuple(observed(value) for value in values))
    if quotients[0][4:] != points['twice'] or quotients[1][4:] != points['triple']:
        raise relation.RelationError('DH precompute quotient output association')
    for offset, window in enumerate(windows):
        if tuple(q[4:] for q in quotients[2 + 3 * offset:5 + 3 * offset]) != (window[1], window[2], window[4]):
            raise relation.RelationError('DH window quotient output association')
    expressions, nodes, derived = _source_cone(obj, roots, domain, copy)
    return dict(metadata=obj, metadata_sha256=hashlib.sha256(data).hexdigest(),
                points=points, windows=windows, quotients=quotients, bits=bits,
                bindings=bindings, expressions=expressions, nodes=nodes, derived=derived,
                qualified=qualified,
                scope='DH closed bounded source/LC ingress; formula/rows/scalar/key/curve/native/caller proofs OPEN')


def _source_cone(obj, roots, domain, copy):
    """Match the observer's exact bounded DAG walk and affine lowering."""
    if not isinstance(obj['expressions'], list) or not 1 <= len(obj['expressions']) <= 4096:
        raise relation.RelationError('DH expression 4096 bound')
    expressions, previous, term_count = {}, (-1, -1), 0
    for item in obj['expressions']:
        if not isinstance(item, dict) or set(item) != {'source', 'terms'}:
            raise relation.RelationError('DH expression shape')
        source = source_index(item['source'])
        relation.terms(item['terms'], domain)
        if source <= previous:
            raise relation.RelationError('DH expression order')
        previous = source
        term_count += len(item['terms'])
        if term_count > 65536:
            raise relation.RelationError('DH total LC term bound')
        terms = tuple((column, int(value, 16)) for column, value in item['terms'])
        if (any(column == copy for column, _ in terms) or
                (source[0] == 0 and any(column != 0 for column, _ in terms)) or
                (source[0] == 1 and terms != ((source[1] + 3, 1),))):
            raise relation.RelationError('DH witness/constant pre-outline LC mismatch')
        expressions[source] = terms
    if not roots <= set(expressions):
        raise relation.RelationError('DH missing role LC')
    if not isinstance(obj['nodes'], list) or len(obj['nodes']) > 8192:
        raise relation.RelationError('DH node 8192 bound')
    nodes, previous = {}, -1
    for item in obj['nodes']:
        if not isinstance(item, dict) or set(item) != {'index', 'multiply', 'left', 'right'}:
            raise relation.RelationError('DH node shape')
        index = relation.natural(item['index'], 2**32)
        left, right = source_index(item['left']), source_index(item['right'])
        if (index <= previous or type(item['multiply']) is not bool or
                any(tag == 2 and child >= index for tag, child in (left, right))):
            raise relation.RelationError('DH source topology')
        previous = index
        nodes[(2, index)] = (item['multiply'], left, right)
    pending, visited, required = list(roots), set(), set(roots)
    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        if len(visited) > 8192:
            raise relation.RelationError('DH source cone bound')
        if source[0] == 2:
            if source not in nodes:
                raise relation.RelationError('DH missing source node')
            multiply, left, right = nodes[source]
            if multiply and left[0] != 0 and right[0] != 0:
                required.update((source, left, right))
            pending.extend((left, right))
        else:
            required.add(source)
    if set(nodes) != {source for source in visited if source[0] == 2} or set(expressions) != required:
        raise relation.RelationError('DH missing/extra graph or expression')
    derived = {}
    for source in sorted(visited):
        if source[0] != 2:
            derived[source] = expressions[source]
            continue
        multiply, left, right = nodes[source]
        if not multiply:
            value = combine(derived[left], derived[right])
        else:
            value = None
            for const, other in ((derived[left], derived[right]), (derived[right], derived[left])):
                if all(column == 0 for column, _ in const):
                    factor = const[0][1] if const else 0
                    value = canonical((column, coefficient * factor) for column, coefficient in other)
                    break
            if value is None:
                value = expressions[source]
        if source in expressions and value != expressions[source]:
            raise relation.RelationError('DH affine LC/source disagreement')
        derived[source] = value
    return expressions, nodes, derived


def inspect_chunks(chunks):
    """Require all eight ordered chunks of ONE occurrence and qualification mode."""
    if not isinstance(chunks, list) or len(chunks) != 8:
        raise relation.RelationError('DH exactly eight chunks required')
    first = chunks[0]
    if type(first.get('qualified')) is not bool:
        raise relation.RelationError('DH chunk qualification mode required')
    shared = ('schema', 'family', 'scope', *IDENTITY, 'role', 'scalar', 'flagged', 'detection_key', 'payload_key',
              'base', 'twice', 'triple', 'output', 'bits', 'total_windows',
              'ordinary_full_ordered_rows_equal', 'repeated_observations_equal')
    expressions, nodes, previous = {}, {}, None
    for ordinal, chunk in enumerate(chunks):
        metadata = chunk['metadata']
        if (metadata['window_start'] != 16 * ordinal or
                metadata['window_count'] != min(16, 126 - 16 * ordinal) or
                any(metadata[key] != first['metadata'][key] for key in shared) or
                chunk.get('qualified') is not first['qualified'] or
                any(metadata[key] is not first['qualified'] for key in
                    ('ordinary_full_ordered_rows_equal', 'repeated_observations_equal')) or
                chunk['quotients'][:2] != first['quotients'][:2]):
            raise relation.RelationError('DH chunk interval/shared role mismatch')
        if previous is not None and chunk['windows'][0][0] != previous:
            raise relation.RelationError('DH cross-chunk accumulator mismatch')
        previous = chunk['windows'][-1][4]
        for accumulated, incoming in ((expressions, chunk['expressions']), (nodes, chunk['nodes'])):
            for handle, value in incoming.items():
                if handle in accumulated and accumulated[handle] != value:
                    raise relation.RelationError('DH cross-chunk source/LC disagreement')
                accumulated[handle] = value
    return dict(chunks=chunks, windows=126, role=first['metadata']['role'],
                expressions=expressions, nodes=nodes, qualified=first['qualified'],
                scope='DH full126 source coverage only; common-assignment kernel/native/caller composition OPEN')


def extract_rows(checked, stream, expected_relation):
    """Recover actual loop/source products and quotient assertions.

    Encryption DH has neither an ownership target assertion nor RNK's output
    inverse. Its operands and output are retained under their actual schema.
    Formula shape and division rows remain separate from curve/nonzero proofs.
    """
    from .transfer_ownership import match_formulas
    from .transfer_arithmetic import extract_templates
    from .transfer_encryption_dh_selection import match_selection
    from .transfer_encryption_dh_boolean import flag_plan, attach_rows
    metadata, derived = checked['metadata'], checked['derived']
    if (metadata.get('schema') != 'shieldd-transfer-encryption-dh-v1' or
            checked.get('qualified') is not True or metadata['relation_digest'] != expected_relation):
        raise relation.RelationError('DH actual qualified occurrence required for row extraction')
    match_selection(checked)
    match_formulas(checked)
    copy = metadata['constant_copy']

    def outline(terms):
        return canonical((copy if column == 0 else column, coefficient) for column, coefficient in terms)

    def observed(value):
        return derived[value[1]] if value[0] == 'source' else canonical([(0, value[1])])

    required, products, squares = {}, [], []

    def require(role, left, right=()):
        required.setdefault((outline(left), outline(right)), []).append(role)

    required[(canonical([(0, 1), (copy, -1)]), ())] = ['constant-copy']
    start, count = metadata['window_start'], metadata['window_count']
    for index in range(2 * (126 - start - count), 2 * (126 - start)):
        bit = derived[checked['bits'][index]]
        require('bit.' + str(index), bit, bit)
    boolean = flag_plan(checked)
    for step in boolean['steps']:
        if step['kind'] == 'assert':
            require(step['obligation'], step['terms'], step['terms'])
    for source, (multiply, left, right) in checked['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0:
            continue
        a, b, output = derived[left], derived[right], derived[source]
        role = 'node.' + str(source[1])
        folded = next(((const, other) for const, other in ((a, b), (b, a))
                       if not const or len(const) == 1 and const[0][0] == 0), None)
        if folded is not None:
            const, other = folded
            factor = const[0][1] if const else 0
            if output != canonical((column, value * factor) for column, value in other):
                raise relation.RelationError('DH folded product LC mismatch')
        elif a == b:
            require(role + '.square', a, output)
        else:
            products.append((role, outline(combine(a, b, -1)), outline(combine(a, b)), outline(output), None))
    for index, quotient in enumerate(checked['quotients']):
        for axis in range(2):
            numerator, denominator, output = map(observed, (quotient[axis], quotient[axis + 2], quotient[axis + 4]))
            role = 'quotient.' + str(index) + '.' + str(axis)
            folded = next(((const, other) for const, other in ((denominator, output), (output, denominator))
                           if not const or len(const) == 1 and const[0][0] == 0), None)
            if folded is not None:
                const, other = folded
                factor = const[0][1] if const else 0
                equation = combine(canonical((column, value * factor) for column, value in other), numerator, -1)
                if equation:
                    require(role + '.assertion', equation)
            elif output == denominator:
                squares.append((role, outline(output), outline(numerator)))
            else:
                products.append((role, outline(combine(output, denominator, -1)),
                                 outline(combine(output, denominator)), None, outline(numerator)))
    extracted = extract_templates(stream, expected_relation, metadata['domain_size'], metadata['full_rows'],
                                  required, products, squares, label='encryption-DH')
    extracted['flag_boolean'] = attach_rows(boolean, extracted)
    extracted['scope'] = 'Actual bounded DH source/loop/Boolean/quotient rows only; scalar/key/curve/nonzero/native/kernel/caller proofs OPEN'
    return extracted


def join_epk(full_occurrence, accepted_epk):
    """Join a qualified DH occurrence to its independently checked fixed EPK.

    Role0 and role1 both use encryption slot0's scalar. Roles2..4 use slots1..3.
    Equal source handles/LCs establish operand association, not native meaning.
    """
    from .transfer_epk_fixed import ALL_PARENT_SCOPE
    if not isinstance(full_occurrence, dict) or full_occurrence.get('qualified') is not True:
        raise relation.RelationError('DH qualified full occurrence required for EPK join')
    full = inspect_chunks(full_occurrence['chunks'])
    if full['qualified'] is not True:
        raise relation.RelationError('DH pending chunks cannot inherit EPK qualification')
    obj = full['chunks'][0]['metadata']
    parent = accepted_epk.get('parent', {}) if isinstance(accepted_epk, dict) else {}
    if (parent.get('schema') != 'shieldd-transfer-epk-all-fixed-pages-v1' or
            parent.get('family') != 'transfer' or parent.get('scope') != ALL_PARENT_SCOPE or
            parent.get('ordinary_full_ordered_rows_equal') is not True or
            parent.get('repeated_observations_equal') is not True or
            any(parent.get(key) != obj[key] for key in IDENTITY) or
            not isinstance(accepted_epk.get('scopes'), list) or len(accepted_epk['scopes']) != 6 or
            not isinstance(accepted_epk.get('parent_sha256'), str) or
            not re.fullmatch('[0-9a-f]{64}', accepted_epk['parent_sha256'])):
        raise relation.RelationError('DH independently typed qualified EPK parent identity')
    slot = 0 if full['role'] == 0 else full['role'] - 1
    selected = accepted_epk['scopes'][2 + slot]
    if (selected.get('lane') != 'encryption' or type(selected.get('slot')) is not int or
            selected['slot'] != slot or not isinstance(selected.get('chunks'), list) or
            len(selected['chunks']) != 8):
        raise relation.RelationError('DH exact EPK encryption slot')
    for ordinal, chunk in enumerate(selected['chunks']):
        epk = chunk['metadata']
        if (epk['window_start'] != 16 * ordinal or epk['window_count'] != min(16, 126 - 16 * ordinal) or
                any(epk[key] != obj[key] for key in IDENTITY) or
                epk['randomizer'] != obj['scalar'] or epk['bits'] != obj['bits'] or
                epk['ordinary_full_ordered_rows_equal'] is not False or
                epk['repeated_observations_equal'] is not False or
                chunk['qualification_parent_sha256'] != accepted_epk['parent_sha256']):
            raise relation.RelationError('DH EPK exact scalar/bit/page-parent association')
    for destination, source in ((full['expressions'], accepted_epk['observed']),
                                (full['nodes'], accepted_epk['nodes'])):
        for handle in set(destination) & set(source):
            if destination[handle] != source[handle]:
                raise relation.RelationError('DH EPK common LC/AST disagreement')
    return dict(role=full['role'], slot=slot, scalar=full['chunks'][0]['bindings']['scalar'],
                bits=full['chunks'][0]['bits'], epk_parent_sha256=accepted_epk['parent_sha256'],
                dh_metadata_sha256=[chunk['metadata_sha256'] for chunk in full['chunks']],
                published=selected['chunks'][0]['metadata']['published'],
                scope='Exact same-source scalar/bits for fixed EPK and variable DH; scalar/native/key/row/kernel/caller meaning OPEN')


def inspect_occurrences(occurrences, accepted_epk):
    """Join all five complete qualified loops to one encryption key/scalar view."""
    from .transfer_encryption_dh_selection import match_selection
    if not isinstance(occurrences, list) or len(occurrences) != 5:
        raise relation.RelationError('DH exactly five full occurrences required')
    full = [inspect_chunks(occurrence['chunks']) for occurrence in occurrences]
    if [occurrence['role'] for occurrence in full] != list(range(5)):
        raise relation.RelationError('DH full occurrence order/coverage mismatch')
    first = full[0]['chunks'][0]['metadata']
    for occurrence in full:
        metadata = occurrence['chunks'][0]['metadata']
        if any(metadata[key] != first[key] for key in (*IDENTITY, 'flagged', 'detection_key', 'payload_key')):
            raise relation.RelationError('DH common flag/key/relation source disagreement')
        for chunk in occurrence['chunks']:
            match_selection(chunk)
    joins = [join_epk(occurrence, accepted_epk) for occurrence in full]
    if joins[0]['scalar'] != joins[1]['scalar'] or joins[0]['bits'] != joins[1]['bits']:
        raise relation.RelationError('DH unconditional/tier0 scalar disagreement')
    expressions, nodes = {}, {}
    for occurrence in full:
        for destination, incoming in ((expressions, occurrence['expressions']), (nodes, occurrence['nodes'])):
            for handle, value in incoming.items():
                if handle in destination and destination[handle] != value:
                    raise relation.RelationError('DH cross-occurrence common LC/AST disagreement')
                destination[handle] = value
    return dict(occurrences=full, epk_joins=joins, expressions=expressions, nodes=nodes,
                qualified=True, windows=5 * 126,
                scope='Five exact qualified126-window DH source/key/EPK operand views; actual row/loop/native/caller/full Transfer proof OPEN')
