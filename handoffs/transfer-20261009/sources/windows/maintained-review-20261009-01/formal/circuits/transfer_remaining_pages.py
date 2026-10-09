"""Closed remaining-caller pages. Qualification is a separate four-spool action.

The retained pending page bytes never acquire qualification flags. An accepted
manifest binds their bytes; exact role, LC, native sponge and source DAG checks
are independent of those identities. Native/group/TransferSem joins stay open.
"""
import hashlib
import re
from blake3 import blake3
from . import transfer_relation as relation, transfer_note_hash as hashes
from . import transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index

SCOPES = ('sender', 'receiver', 'volume', 'encryption', 'audit-sender',
          'audit-receiver', 'routing', 'statement')
CALL_ORDER = ('sender', 'receiver', 'volume', 'audit-sender', 'audit-receiver',
              'encryption', 'routing', 'statement')
IDENTITY = ('relation_digest', 'domain_size', 'full_rows', 'constant_copy')
FLAGS = ('ordinary_full_ordered_rows_equal', 'repeated_observations_equal')
STATUS = 'typed source/LC observations only; ordinary/repeat/kernel/native joins open'


def roster(scope):
    if scope in ('sender', 'receiver'): return [(19, 9)] + [(3, 5)] * 16
    if scope == 'volume': return [(4, 5), (5, 4)] + [(1, 5)] * 24 + [(6, 3), (7, 3), (5, 4), (9, 3), (8, 3)]
    if scope == 'encryption':
        return [(14, 2)] * 5 + [(12, 4)] + [(10, 2)] * 4 + [(11, 2), (13, 4), (10, 2)] * 2 + [(11, 2), (10, 2), (10, 2), (10, 2)] * 2
    if scope in ('audit-sender', 'audit-receiver'): return [(35, 4)]
    if scope == 'routing': return [(33, 3), (30, 2), (30, 2), (32, 1), (31, 2), (31, 2)]
    if scope == 'statement': return [(34, 64)]
    raise relation.RelationError('remaining unsupported scope')


def descriptors(scope):
    result = [(None, 0)]
    index = 0
    for owner in CALL_ORDER:
        for _, arity in roster(owner):
            if owner == scope:
                result.extend((index, b) for b in range((arity + (1 if arity <= 2 else 4)) // (2 if arity <= 2 else 5)))
            index += 1
    return result


def shapes():
    result = {('caller', tag, 0): width for tag, width in
              [('shared', 8), ('registry-leaf', 14), ('auth-roots', 7), ('note-slots', 8), ('external', 2), ('balance', 2)]}
    for owner in ('sender', 'receiver'):
        result.update({(owner, tag, 0): width for tag, width in
                       [('membership', 5), ('computed-root', 1), ('lifecycle-bits', 131), (owner + '-binding', 8)]})
        result.update({(owner, 'tree-level', i): 14 for i in range(16)})
    result.update({('volume', tag, 0): width for tag, width in
                   [('shared', 12), ('context-bool', 2), ('day-index', 1), ('timestamp-bits', 64), ('day-bits', 48),
                    ('second-within', 1), ('prior-bits', 128), ('successor-bits', 128), ('controls', 13),
                    ('candidate-bits', 128), ('limit-bits', 128), ('second-bits', 17), ('volume-output', 5)]})
    result.update({('volume', 'tree-level', i): 14 for i in range(24)})
    result.update({('encryption', tag, 0): width for tag, width in
                   [('shared', 24), ('audit-output', 6), ('published44', 44), ('metadata-equality-endpoints', 20)]})
    result.update({('encryption', 'ephemeral-bits', i): 252 for i in range(4)})
    for owner in ('audit-sender', 'audit-receiver'):
        result.update({(owner, 'randomness-bits', 0): 252, (owner, 'binding', 0): 10})
    result.update({('routing', tag, 0): width for tag, width in
                   [('shared', 7), ('precision-values', 2), ('regulated-prefix', 32), ('unregulated-prefix', 32),
                    ('active-prefix', 32), ('flags', 7), ('routing-output', 4)]})
    for slot in range(2):
        result.update({('routing', tag, slot): width for tag, width in
                       [('public-bits', 32), ('route-bits', 255), ('random-bits', 255)]})
    result.update({('statement', 'ordered64', 0): 64, ('statement', 'interface', 0): 2})
    return result


def require(condition, message):
    if not condition: raise relation.RelationError('remaining ' + message)


def reference(value):
    require(isinstance(value, dict) and len(value) == 1, 'reference shape')
    if set(value) == {'source'}: return ('source', source_index(value['source']))
    require(set(value) == {'native'} and isinstance(value['native'], str)
            and re.fullmatch('[0-9a-f]{64}', value['native'])
            and int(value['native'], 16) < relation.MODULUS, 'canonical native reference')
    return ('native', int(value['native'], 16))


def inspect_manifest(data, expected_relation):
    require(isinstance(data, bytes) and len(data) <= 128 * 1024, 'manifest byte bound')
    obj = relation.record(data)
    require(set(obj) == {'schema', 'family', 'scope', 'pages', 'qualification', 'semantic_status', *IDENTITY, *FLAGS}
            and obj['schema'] == 'shieldd-transfer-remaining-source-pages-v1'
            and obj['family'] == 'transfer' and obj['scope'] in SCOPES
            and obj['qualification'] is False and obj['semantic_status'] == STATUS, 'closed manifest')
    require(obj['relation_digest'] == expected_relation and isinstance(expected_relation, str)
            and re.fullmatch('[0-9a-f]{64}', expected_relation)
            and all(obj[k] is True for k in FLAGS), 'qualified ordinary/repeat identity')
    require((relation.natural(obj['domain_size']), relation.natural(obj['full_rows']),
             relation.natural(obj['constant_copy'])) == (262144, 200770, 200692), 'actual Transfer shape')
    wanted = descriptors(obj['scope'])
    require(isinstance(obj['pages'], list) and len(obj['pages']) == len(wanted), 'exact component page inventory')
    for ordinal, (item, (index, block)) in enumerate(zip(obj['pages'], wanted)):
        require(isinstance(item, dict) and set(item) == {'ordinal', 'suffix', 'bytes', 'blake3', 'hash', 'block'}, 'closed descriptor')
        require(type(item['ordinal']) is int and item['ordinal'] == ordinal and type(item['block']) is int
                and item['block'] == block and item['suffix'] == f'pending-page-{ordinal:03}.json'
                and (item['hash'] is None if index is None else type(item['hash']) is int and item['hash'] == index), 'ordered descriptor')
        require(type(item['bytes']) is int and 0 < item['bytes'] <= 4 * 1024 * 1024
                and isinstance(item['blake3'], str) and re.fullmatch('[0-9a-f]{64}', item['blake3']), 'descriptor bytes/digest')
    return obj


def report(records, calls):
    require(isinstance(records, list) and len(records) == 110, 'exact record count')
    result = {}
    wanted = shapes()
    bit_handles = set()
    for entry in records:
        require(isinstance(entry, dict) and set(entry) == {'scope', 'tag', 'ordinal', 'values'}, 'record shape')
        require(isinstance(entry['scope'], str) and isinstance(entry['tag'], str)
                and type(entry['ordinal']) is int, 'record types')
        key = (entry['scope'], entry['tag'], entry['ordinal'])
        require(key in wanted and key not in result and isinstance(entry['values'], list)
                and len(entry['values']) == wanted[key], 'record order/width/duplicate')
        for value in entry['values']: reference(value)
        if entry['tag'].endswith('-bits'):
            handles = [reference(value) for value in entry['values']]
            require(all(kind == 'source' and handle[0] == 1 for kind, handle in handles)
                    and len(set(handles)) == len(handles) and not bit_handles.intersection(handles),
                    'bit witness alias/native/overlap')
            bit_handles.update(handles)
        result[key] = entry['values']
    require(set(result) == set(wanted), 'complete record inventory')
    require(isinstance(calls, list) and len(calls) == 98, 'exact hash call count')
    order = [(scope, domain, arity) for scope in CALL_ORDER for domain, arity in roster(scope)]
    for call, (scope, domain, arity) in zip(calls, order):
        require(isinstance(call, dict) and set(call) == {'scope', 'domain', 'inputs', 'output', 'blocks'}
                and call['scope'] == scope and type(call['domain']) is int and call['domain'] == domain
                and isinstance(call['inputs'], list) and len(call['inputs']) == arity, 'hash scope/domain/arity/order')
        for value in call['inputs'] + [call['output']]: reference(value)
        width, rate = (3, 2) if arity <= 2 else (6, 5)
        require(isinstance(call['blocks'], list) and len(call['blocks']) == (arity + rate - 1) // rate, 'hash block inventory')
        for block in call['blocks']:
            require(isinstance(block, dict) and set(block) == {'before', 'after'}
                    and all(isinstance(block[k], list) and len(block[k]) == width for k in ('before', 'after')), 'hash checkpoint width')
            for value in block['before'] + block['after']: reference(value)
        require(call['output'] == call['blocks'][-1]['after'][1], 'hash output lane/source')
    _joins(result, calls)
    return result


def _joins(r, calls):
    at = lambda scope, tag: r[scope, tag, 0]
    shared, leaf, auth, notes = (at('caller', tag) for tag in ('shared', 'registry-leaf', 'auth-roots', 'note-slots'))
    sender, receiver = at('sender', 'sender-binding'), at('receiver', 'receiver-binding')
    vol, ctl, vo = (at('volume', tag) for tag in ('shared', 'controls', 'volume-output'))
    enc, published, metadata, endpoints = (at('encryption', tag) for tag in ('shared', 'published44', 'audit-output', 'metadata-equality-endpoints'))
    route, ro = at('routing', 'shared'), at('routing', 'routing-output')
    require(vol[0] == shared[4] and vol[2:6] == sender[:4] and vol[6] == shared[3]
            and vol[7] == notes[6] and vol[8] == leaf[9] and vol[9] == shared[0]
            and vol[10] == auth[0] and vol[11] == shared[5], 'volume exact caller/raw NK/outbound slot')
    require(at('caller', 'external')[1] == shared[7], 'external regulated alias')
    require(enc[0] == vo[4] and enc[1] == shared[5] and enc[2] == shared[3] and enc[3] == notes[6]
            and enc[11:15] == sender[:4] and enc[15:19] == receiver[:4] and enc[23] == shared[4], 'encryption exact shared inputs')
    require(route[0] == shared[7] and route[1] == notes[7] and route[2:4] == sender[2:4]
            and route[4:6] == receiver[2:4] and route[6] == shared[5], 'routing exact change slot/address/nonce')
    require(ctl[2] == vo[3] and ctl[6] == vo[2] and ctl[12] == vo[4]
            and at('volume', 'context-bool')[0] == vo[3], 'volume output/context aliases')
    hs = lambda scope: [h for h in calls if h['scope'] == scope]
    for owner, bound in [('sender', sender), ('receiver', receiver)]:
        member, h = at(owner, 'membership'), hs(owner)
        require(member[2:] == [shared[3], shared[2], shared[7]]
                and h[0]['inputs'] == bound[:4] + [shared[3]] + bound[4:]
                and h[0]['output'] == member[0], 'compliance caller/leaf binding')
        for level in range(16):
            tree = r[owner, 'tree-level', level]
            require(tree[0] == h[level]['output'] and tree[8:12] == h[level+1]['inputs'][1:]
                    and tree[12] == h[level+1]['output'] and tree[13] == member[1]
                    and h[level+1]['inputs'][0] == {'native': f'{level+1:064x}'}, 'compliance ordered tree edge')
        require(at(owner, 'computed-root')[0] == h[-1]['output'], 'compliance final root')
    h = hs('volume')
    require(h[0]['inputs'] == sender[:4] + [shared[3]], 'volume subject input')
    for level in range(24):
        tree = r['volume', 'tree-level', level]
        require(tree[0] == h[level+1]['output'] and tree[8:12] == h[level+2]['inputs'][1:]
                and tree[12] == h[level+2]['output']
                and h[level+2]['inputs'][0] == {'native': f'{level+1:064x}'}, 'volume ordered tree edge')
    require(all(h[i]['inputs'][0] == auth[0] for i in (26, 27, 29, 30)), 'volume raw NK source')
    # These are argument identities from volume::constrain, rather than the
    # gated value equalities or desired hash results. In particular the
    # witness subject is distinct from the separately computed subject hash.
    position = r['volume', 'tree-level', 0][13]
    require(all(r['volume', 'tree-level', i][13] == position for i in range(24)),
            'volume same prior-path position source')
    require(h[1]['inputs'][:3] == [ctl[7], ctl[6], ctl[8]]
            and h[26]['inputs'] == [auth[0], ctl[7], ctl[6]]
            and h[27]['inputs'] == [auth[0], h[1]['output'], position]
            and h[28]['inputs'][:3] == [ctl[7], ctl[6], ctl[9]]
            and all(h[i]['inputs'] == [auth[0], vol[11], ctl[6]] for i in (29, 30)),
            'volume exact prior/successor/origin/previous/padding constructor inputs')
    for owner, bound, start in [('audit-sender', sender, 36), ('audit-receiver', receiver, 40)]:
        binding = at(owner, 'binding')
        require(binding[:4] == bound[:4] and binding[4:6] == enc[9:11]
                and hs(owner)[0]['inputs'] == binding[:4] and binding[6:] == published[start:start+4], 'ownership caller/published slot')
    require(metadata == published[26:31] + [published[35]], 'published metadata aliases')
    require(all(endpoints[2*i:2*i+2] == [published[26+i], enc[19+i]] for i in range(5))
            and endpoints[10:12] == [published[35], enc[6]]
            and all(endpoints[12+2*i:14+2*i] == [published[31+i], hs('encryption')[i+1]['output']] for i in range(4)),
            'metadata equality endpoints (field equality remains a row obligation)')
    ordered = auth[4:6] + [shared[0]] + notes[2:6] + at('caller', 'balance') + ro[1:3] + [ro[0]] + vo[:4] + notes[:2] + shared[1:3] + published[:4]
    for core, ext in [(4, 14), (9, 20)]: ordered += published[core:core+3] + [published[core+4]] + published[ext:ext+6]
    ordered += [shared[4], published[7], published[12]] + published[26:30] + published[31:44]
    require(len(ordered) == 64 and ordered == at('statement', 'ordered64')
            and hs('statement')[0]['inputs'] == ordered and at('statement', 'interface')[1] == shared[6], 'ordered64 exact roots/commitment alias')


def inspect_page(manifest_data, data, ordinal, accepted_roles, parameter_root=None):
    accepted = accepted_roles['metadata']
    manifest = inspect_manifest(manifest_data, accepted['relation_digest'])
    require(all(manifest[k] == accepted[k] for k in IDENTITY), 'accepted caller full relation identity')
    ordinal = relation.natural(ordinal, len(manifest['pages']))
    descriptor = manifest['pages'][ordinal]
    require(isinstance(data, bytes) and len(data) == descriptor['bytes']
            and blake3(data).hexdigest() == descriptor['blake3'], 'exact pending page bytes')
    obj = relation.record(data)
    require(set(obj) == {'schema', 'family', 'scope', 'ordinal', 'qualification', *FLAGS,
                         'records', 'calls', 'hash', 'nodes', 'expressions'}
            and obj['schema'] == 'shieldd-transfer-remaining-source-page-v1'
            and obj['family'] == 'transfer' and obj['scope'] == manifest['scope']
            and type(obj['ordinal']) is int and obj['ordinal'] == ordinal
            and obj['qualification'] is False and all(obj[k] is False for k in FLAGS), 'closed pending page')
    records = report(obj['records'], obj['calls'])
    caller = accepted['caller']
    require(records['sender', 'sender-binding', 0][:4] == caller['address']
            and records['caller', 'shared', 0][3] == caller['asset']
            and records['caller', 'shared', 0][7] == caller['regulated']
            and records['caller', 'auth-roots', 0][:4] == [caller['nk'], caller['effective_nk'], *caller['ak']], 'accepted authorization exact role ties')
    observed = _expressions(obj['expressions'], manifest['domain_size'], manifest['constant_copy'], 4096, 'remaining')
    for handle, lc in observed.items():
        require(handle not in accepted_roles['observed'] or accepted_roles['observed'][handle] == lc, 'accepted caller shared LC')
    checked = dict(metadata={**obj, **{k: manifest[k] for k in IDENTITY}}, observed=observed,
                   records=records, metadata_sha256=hashlib.sha256(data).hexdigest(), block=descriptor['block'])
    required = set()
    def value(ref):
        kind, item = reference(ref)
        if kind == 'native': return canonical([(0, item)])
        required.add(item); require(item in observed, 'selected source LC coverage')
        return observed[item]
    if ordinal == 0:
        require(obj['hash'] is None and obj['nodes'] == [], 'roles page has no permutation claim')
        for (scope, _, _), values in records.items():
            if scope in ('caller', obj['scope']):
                for ref in values: value(ref)
        require(set(observed) == required, 'roles exact LC selection')
        return checked
    index, block = descriptors(manifest['scope'])[ordinal]
    call = obj['calls'][index]
    require(obj['hash'] == {**call, 'index': index, 'block': block}, 'selected hash exact global call')
    inputs = [value(ref) for ref in call['inputs']]
    width, rate = (3, 2) if len(inputs) <= 2 else (6, 5)
    state = [canonical([(0, call['domain'] + 256 * len(inputs))])] + [()] * (width - 1)
    for b, part in enumerate(call['blocks']):
        expected = list(state)
        for lane, item in enumerate(inputs[rate*b:rate*(b+1)], 1): expected[lane] = combine(expected[lane], item)
        require([value(ref) for ref in part['before']] == expected, 'native domain/arity absorbed state LCs')
        state = [value(ref) for ref in part['after']]
    require(value(call['output']) == state[1], 'hash output LC')
    checked['metadata']['hash'] = {k: call[k] for k in ('domain', 'inputs', 'output', 'blocks')}
    checked['metadata'].update(slot=0, role=manifest['scope'], level=index, block=block)
    checked['boundary_sources'] = required
    require(parameter_root is not None, 'independent pinned Poseidon parameters required')
    return hashes._inspect_permutation(checked, parameter_root, width=width)


def extract_metadata_equalities(manifest_data, page_data, stream, accepted_roles):
    checked = inspect_page(manifest_data, page_data, 0, accepted_roles)
    require(checked['metadata']['scope'] == 'encryption', 'encryption role page required for metadata rows')
    obj = checked['metadata']; endpoints = checked['records']['encryption', 'metadata-equality-endpoints', 0]
    def value(ref):
        kind, item = reference(ref)
        return canonical([(0, item)]) if kind == 'native' else checked['observed'][item]
    outline = lambda lc: canonical((obj['constant_copy'] if c == 0 else c, v) for c, v in lc)
    required = {(canonical([(0, 1), (obj['constant_copy'], -1)]), ()): ['constant-copy']}
    for i in range(10):
        delta = combine(value(endpoints[2*i]), value(endpoints[2*i+1]), -1)
        require(bool(delta), 'independent equality endpoints collapsed to an LC alias')
        required.setdefault((outline(delta), ()), []).append('metadata-equality.' + str(i))
    extracted = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                             required, [], [], label='remaining-metadata-equalities')
    extracted.update(metadata_sha256=checked['metadata_sha256'], scope='ten exact published/shared metadata equality rows; native encryption/TransferSem open')
    return extracted


def extract_hash(manifest_data, page_data, ordinal, stream, accepted_roles, parameter_root):
    checked = inspect_page(manifest_data, page_data, ordinal, accepted_roles, parameter_root)
    require(ordinal != 0, 'permutation page required')
    return hashes._extract_permutation(checked, stream, label='remaining-' + checked['metadata']['scope'])


def metadata_certificates(manifest_data, page_data, extracted, accepted_roles):
    checked = inspect_page(manifest_data, page_data, 0, accepted_roles)
    require(checked['metadata']['scope'] == 'encryption', 'encryption metadata certificate scope')
    raw, rows = arithmetic.normalize_selection(extracted, checked['metadata'], checked['metadata_sha256'])
    endpoints = checked['records']['encryption', 'metadata-equality-endpoints', 0]
    def value(ref):
        kind, item = reference(ref)
        return canonical([(0, item)]) if kind == 'native' else checked['observed'][item]
    bindings = []; used = set()
    for i in range(10):
        left, right = value(endpoints[2*i]), value(endpoints[2*i+1])
        delta = combine(left, right, -1)
        require(bool(delta), 'metadata distinct LC endpoints')
        matches = [j for j, row in rows.items() if row in ((delta, ()), (canonical((c, -v) for c, v in delta), ()))]
        require(len(matches) == 1, 'metadata actual equality row missing/ambiguous')
        used.update(matches); bindings.append((left, right, rows[matches[0]][0] == delta))
    copy = checked['metadata']['constant_copy']
    link = [j for j, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    require(len(link) == 1 and used | set(link) == set(raw), 'metadata exact physical row coverage')
    return dict(checked=checked, raw=raw, bindings=bindings)


def generate_metadata_bindings(manifest_data, page_data, extracted, accepted_roles):
    """Only actual finite equality rows; native encryption remains a later join."""
    from .generate_hash_round import linear, _signature_audits
    selected = metadata_certificates(manifest_data, page_data, extracted, accepted_roles)
    copy = selected['checked']['metadata']['constant_copy']
    source = ('import ShielddSecurity.Compiler\nset_option maxHeartbeats 600000\n'
              'namespace ShielddSecurity.RuntimeTransferMetadataBindings\n'
              'open ShielddSecurity\n' + f'def modulus : Nat := {relation.MODULUS}\n'
              'def rawRows : List Row := [\n' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩' for a, b in selected['raw'].values()) + ']\n'
              + f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n'
              + f'theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n')
    names = ['ring_id_binding', 'policy_id_binding', 'resource_binding', 'permission_binding',
             'timestamp_binding', 'epoch_binding', 'salt0_binding', 'salt1_binding', 'salt2_binding', 'salt3_binding']
    for name, (left, right, direct) in zip(names, selected['bindings']):
        first, second = (left, right) if direct else (right, left)
        proof = f'Compiler.checked_assertion_sound rho rows {linear(first)} {linear(second)} normalized (by decide)'
        if not direct: proof = '(' + proof + ').symm'
        source += f'''theorem {name} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(left)} = eval rho {linear(right)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  exact {proof}
'''
    for name in ['constantLink', *names]: source += '#print axioms ' + name + '\n'
    return _signature_audits(source + 'end ShielddSecurity.RuntimeTransferMetadataBindings\n')


def tree_level_obligations(manifest_data, page_data, level, accepted_roles):
    """One actual ordered tree record; no node/child value is assumed."""
    checked = inspect_page(manifest_data, page_data, 0, accepted_roles)
    obj = checked['metadata']; scope = obj['scope']
    require(scope in ('sender', 'receiver', 'volume'), 'tree role page scope')
    depth = 24 if scope == 'volume' else 16
    level = relation.natural(level, depth)
    refs = checked['records'][scope, 'tree-level', level]
    def value(ref):
        kind, item = reference(ref)
        return canonical([(0, item)]) if kind == 'native' else checked['observed'][item]
    values = [value(ref) for ref in refs]
    node, low, high, first, second, third, left_swap, right_swap = values[:8]
    children = values[8:12]
    left_first = combine(node, left_swap)
    left_second = combine(first, left_swap, -1)
    right_third = combine(node, right_swap)
    right_fourth = combine(third, right_swap, -1)
    products = [
        ('left_swap', low, combine(first, node, -1), left_swap),
        ('right_swap', low, combine(third, node, -1), right_swap),
    ]
    for i, (yes, base) in enumerate(zip(
            (first, second, right_third, right_fourth),
            (left_first, left_second, second, third))):
        products.append(('select' + str(i), high, combine(yes, base, -1),
                         combine(children[i], base, -1)))
    require(all(len(bit) == 1 and bit[0][1] == 1 and bit[0][0] not in
                (0, obj['constant_copy']) for bit in (low, high))
            and low != high, 'actual distinct tree Boolean witnesses')
    return dict(checked=checked, level=level, depth=depth, values=values,
                products=products)


def _tree_level_requirements(selected):
    obj = selected['checked']['metadata']; copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c, v) for c, v in lc)
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy']}
    for name, bit in zip(('low', 'high'), selected['values'][1:3]):
        required.setdefault((outline(bit), outline(bit)), []).append(name + '-Boolean')
    products = []
    for name, left, right, output in selected['products']:
        if not left or not right or (len(left) == 1 and left[0][0] == 0) or (len(right) == 1 and right[0][0] == 0):
            arithmetic.product_certificate(left, right, output, {})
        elif left == right:
            required.setdefault((outline(left), outline(output)), []).append(name + '-square')
        else:
            products.append((name, outline(combine(left, right, -1)),
                             outline(combine(left, right)), outline(output), None))
    return required, products, []


def extract_tree_level(manifest_data, page_data, level, stream, accepted_roles):
    """Replay exact original Boolean/product rows; one bounded path level."""
    selected = tree_level_obligations(manifest_data, page_data, level, accepted_roles)
    obj = selected['checked']['metadata']
    required, products, squares = _tree_level_requirements(selected)
    extracted = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                             required, products, squares, label='remaining-tree-level')
    extracted.update(metadata_sha256=selected['checked']['metadata_sha256'],
                     tree_level=selected['level'], tree_scope=obj['scope'],
                     scope='exact one-level quaternary Boolean/product wiring only; position/hash/root/lifecycle/native/TransferSem joins open')
    return extracted


def tree_level_certificates(manifest_data, page_data, level, extracted, accepted_roles):
    selected = tree_level_obligations(manifest_data, page_data, level, accepted_roles)
    obj = selected['checked']['metadata']
    require(type(extracted.get('tree_level')) is int and extracted['tree_level'] == selected['level']
            and extracted.get('tree_scope') == obj['scope'], 'extraction exact tree scope/level')
    raw, normalized = arithmetic.normalize_selection(extracted, obj, selected['checked']['metadata_sha256'])
    used = set(); boolean_rows = []
    for bit in selected['values'][1:3]:
        indices = [i for i, row in normalized.items() if row == (bit, bit)]
        require(len(indices) == 1, 'tree actual Boolean row missing/ambiguous')
        used.update(indices); boolean_rows.extend(indices)
    certificates = {}
    for name, left, right, output in selected['products']:
        certificate = arithmetic.product_certificate(left, right, output, normalized)
        certificates[name] = certificate; used.update(certificate['rows'])
    copy = obj['constant_copy']
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    require(len(links) == 1 and used | set(links) == set(raw), 'tree exact selected physical-row coverage')
    selected.update(raw=raw, normalized=normalized, certificates=certificates,
                    boolean_rows=boolean_rows)
    return selected


def generate_tree_level(manifest_data, page_data, level, extracted, accepted_roles):
    """Derive real children on arbitrary assignments from selected original rows."""
    from .generate_hash_round import linear, signed, _signature_audits
    selected = tree_level_certificates(manifest_data, page_data, level, extracted, accepted_roles)
    obj = selected['checked']['metadata']; copy = obj['constant_copy']
    namespace = 'RuntimeTransfer' + obj['scope'].capitalize() + f'TreeLevel{level:03}'
    fields = ['node', 'low', 'high', 'first', 'second', 'third', 'leftSwap', 'rightSwap',
              'child0', 'child1', 'child2', 'child3', 'nextRoot', 'position']
    out = ['import ShielddSecurity.Tree\nimport ShielddSecurity.ScalarRows\n',
           f'namespace ShielddSecurity.{namespace}\nset_option maxHeartbeats 300000\n',
           f'def modulus : Nat := {relation.MODULUS}\n',
           'def originalRows : List Nat := ' + str(sorted(selected['raw'])) + '\n',
           'def rawRows : List Row := [' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩'
                for a, b in selected['raw'].values()) + ']\n',
           f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n',
           f'theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n',
           '''theorem fourNonzero {F : Type} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
''']
    exports = ['constantLink', 'fourNonzero']
    for name, lc in zip(fields, selected['values']): out.append(f'def {name} : Linear := {linear(lc)}\n')
    for name, left, right, output in selected['products']:
        c = selected['certificates'][name]
        for suffix, lc in [('left', left), ('right', right), ('output', output)]:
            out.append(f'def {name}_{suffix} : Linear := {linear(lc)}\n')
        datum = ('.product ' + linear(c['auxiliary']) if c['kind'] == 'product' else '.square' if c['kind'] == 'square'
                 else ('.foldedLeft ' if c['kind'] == 'folded_left' else '.foldedRight ') + f'({signed(c["coefficient"])} : Int)')
        a, b = (name + '_right', name + '_left') if c.get('swapped') else (name + '_left', name + '_right')
        out.append(f'''theorem {name}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {name}_output = eval rho {name}_left * eval rho {name}_right := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product := ScalarRows.checked_product_sound rho one (fourNonzero (F := F)) rows normalized
    {a} {b} {name}_output ({datum}) (by decide)
  simpa only [mul_comm] using product
'''); exports.append(name + '_sound')
    out.append('''private theorem select_from_product {F : Type} [Field F]
    (bit yes base child : F) (product : child - base = bit * (yes - base)) :
    child = Tree.select bit yes base := by
  calc
    child = (child - base) + base := by ring
    _ = bit * (yes - base) + base := by rw [product]
    _ = Tree.select bit yes base := by unfold Tree.select; ring
''')
    # LC identities are checked canonically; exact captured values remain the
    # only evaluation arguments. The next hash/root and position are not proved.
    out.append(f'''theorem actual_children {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    ∃ lowBit highBit : Bool, Tree.bit lowBit = eval rho low ∧
      Tree.bit highBit = eval rho high ∧
      [eval rho child0, eval rho child1, eval rho child2, eval rho child3] =
        Tree.children lowBit highBit (eval rho node) (eval rho first) (eval rho second) (eval rho third) := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have lowBoolean : Square (eval rho low) (eval rho low) :=
    Compiler.checked_row_sound rho rows ⟨low,low⟩ normalized (by decide)
  have highBoolean : Square (eval rho high) (eval rho high) :=
    Compiler.checked_row_sound rho rows ⟨high,high⟩ normalized (by decide)
''')
    for name, left, right, output in selected['products']:
        # Use certified canonical LC subtraction instead of an evaluation
        # premise about the intended product or selected child.
        if name in ('left_swap', 'right_swap'):
            sibling = 'first' if name == 'left_swap' else 'third'
            swap = 'leftSwap' if name == 'left_swap' else 'rightSwap'
            out.append(f'''  have {name}Value : eval rho {swap} = eval rho low * (eval rho {sibling} - eval rho node) := by
    have product := {name}_sound rho one satisfied
    have diff := Compiler.canonical_equal rho {name}_right (Compiler.subtract {sibling} node) (by decide)
    rw [Compiler.eval_subtract] at diff
    simpa only [{name}_output, {swap}, {name}_left, low, diff] using product
''')
        else:
            i = int(name[-1]); yes = ['first', 'second', '(node ++ rightSwap)', '(Compiler.subtract third rightSwap)'][i]
            base = ['(node ++ leftSwap)', '(Compiler.subtract first leftSwap)', 'second', 'third'][i]
            out.append(f'''  have {name}Value : eval rho child{i} = Tree.select (eval rho high) (eval rho {yes}) (eval rho {base}) := by
    have product := {name}_sound rho one satisfied
    have result := Compiler.canonical_equal rho {name}_output (Compiler.subtract child{i} {base}) (by decide)
    have difference := Compiler.canonical_equal rho {name}_right (Compiler.subtract {yes} {base}) (by decide)
    rw [Compiler.eval_subtract] at result difference
    apply select_from_product
    rw [← result, ← difference]
    simpa only [{name}_left, high] using product
''')
    out.append('''  have wired : [eval rho child0, eval rho child1, eval rho child2, eval rho child3] =
      Tree.wiredChildren (eval rho low) (eval rho high) (eval rho node)
        (eval rho first) (eval rho second) (eval rho third) := by
    simp only [select0Value, select1Value, select2Value, select3Value,
      eval_append, Compiler.eval_subtract, Tree.wiredChildren,
      left_swapValue, right_swapValue]
  obtain ⟨lo,hi,lowValue,highValue,children⟩ := Tree.wiring_sound
    (eval rho low) (eval rho high) (eval rho node) (eval rho first)
    (eval rho second) (eval rho third) lowBoolean highBoolean
  exact ⟨lo,hi,lowValue,highValue,wired.trans children⟩
'''); exports.append('actual_children')
    for name in exports: out.append('#print axioms ' + name + '\n')
    return _signature_audits(''.join(out) + f'end ShielddSecurity.{namespace}\n')


def tree_position_obligations(manifest_data, page_data, accepted_roles):
    """Bind ordered low/high pairs to the actual tree position assertion."""
    checked = inspect_page(manifest_data, page_data, 0, accepted_roles)
    obj = checked['metadata']; scope = obj['scope']
    require(scope in ('sender', 'receiver', 'volume'), 'tree position role page scope')
    depth = 24 if scope == 'volume' else 16
    def value(ref):
        kind, item = reference(ref)
        return canonical([(0, item)]) if kind == 'native' else checked['observed'][item]
    levels = [checked['records'][scope, 'tree-level', i] for i in range(depth)]
    position = value(levels[0][13])
    require(all(level[13] == levels[0][13] for level in levels), 'tree same position source at every level')
    bits = [value(ref) for level in levels for ref in level[1:3]]
    require(all(len(bit) == 1 and bit[0][1] == 1 and bit[0][0] not in (0, obj['constant_copy'])
                for bit in bits) and len(set(bits)) == 2*depth, 'tree ordered distinct Boolean positions')
    weighted = canonical((bit[0][0], 2**i) for i, bit in enumerate(bits))
    delta = combine(weighted, position, -1)
    require(bool(delta), 'tree position reconstruction must be an actual assertion')
    return dict(checked=checked, depth=depth, bits=bits, position=position, weighted=weighted, delta=delta)


def _tree_position_requirements(selected):
    obj = selected['checked']['metadata']; copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c, v) for c, v in lc)
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy']}
    for i, bit in enumerate(selected['bits']): required[(outline(bit), outline(bit))] = [f'position-bit-{i}']
    required[(outline(selected['delta']), ())] = ['position-reconstruction']
    return required, [], []


def extract_tree_position(manifest_data, page_data, stream, accepted_roles):
    selected = tree_position_obligations(manifest_data, page_data, accepted_roles)
    obj = selected['checked']['metadata']
    required, products, squares = _tree_position_requirements(selected)
    extracted = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                             required, products, squares, label='remaining-tree-position')
    extracted.update(metadata_sha256=selected['checked']['metadata_sha256'], tree_scope=obj['scope'],
                     scope='exact ordered tree bits and position assertion only; hashes/root/lifecycle/native joins open')
    return extracted


def tree_position_certificates(manifest_data, page_data, extracted, accepted_roles):
    selected = tree_position_obligations(manifest_data, page_data, accepted_roles)
    obj = selected['checked']['metadata']
    require(extracted.get('tree_scope') == obj['scope'], 'tree position extraction exact scope')
    raw, rows = arithmetic.normalize_selection(extracted, obj, selected['checked']['metadata_sha256'])
    used = set()
    for bit in selected['bits']:
        found = [i for i, row in rows.items() if row == (bit, bit)]
        require(len(found) == 1, 'tree position actual Boolean row missing/ambiguous')
        used.update(found)
    delta = selected['delta']; reverse = canonical((c, -v) for c, v in delta)
    assertions = [(i, row[0] == delta) for i, row in rows.items() if row in ((delta, ()), (reverse, ()))]
    require(len(assertions) == 1, 'tree position actual reconstruction row missing/ambiguous')
    used.add(assertions[0][0]); copy = obj['constant_copy']
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    require(len(links) == 1 and used | set(links) == set(raw), 'tree position exact physical-row coverage')
    selected.update(raw=raw, direct=assertions[0][1])
    return selected


def generate_tree_position(manifest_data, page_data, extracted, accepted_roles):
    """Unbounded-assignment range consequence from real ordered bit/assertion rows."""
    from .generate_hash_round import linear, _signature_audits
    selected = tree_position_certificates(manifest_data, page_data, extracted, accepted_roles)
    obj = selected['checked']['metadata']; copy = obj['constant_copy']; width = 2*selected['depth']
    ns = 'RuntimeTransfer' + obj['scope'].capitalize() + 'TreePosition'
    first, second = ('weightedValue', 'position') if selected['direct'] else ('position', 'weightedValue')
    source = f'''import ShielddSecurity.Compiler
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 400000
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {list(selected['raw'])}
def rawRows : List Row := [''' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩' for a, b in selected['raw'].values()) + f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def bits : List Nat := {[bit[0][0] for bit in selected['bits']]}
def position : Linear := {linear(selected['position'])}
def weightedValue : Linear := {linear(selected['weighted'])}
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
theorem ordered_bits_boolean {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ∀ x ∈ bits.map rho, Square x x := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have certificates : bits.all (fun column => Compiler.checkRow modulus rows (booleanRow column)) = true := by decide
  intro x present
  obtain ⟨column, member, rfl⟩ := List.mem_map.mp present
  have checked := Compiler.checked_row_sound rho rows (booleanRow column) normalized
    ((List.all_eq_true.mp certificates) column member)
  simpa only [booleanRow, eval, Int.cast_one, one_mul, add_zero] using checked
theorem ordered_position {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    fieldBinary (bits.map rho) = eval rho position := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have actual := Compiler.checked_assertion_sound rho rows {first} {second} normalized (by decide)
  {'have actual := actual.symm' if not selected['direct'] else ''}
  have semantic := Compiler.canonical_equal rho weightedValue (weighted bits 1) (by decide)
  rw [weighted_eval] at semantic
  simp only [Int.cast_one, one_mul] at semantic
  exact semantic.symm.trans actual
theorem actual_position_bound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ∃ n : Nat, n < 2^{width} ∧ (n : F) = eval rho position := by
  have result := range_sound (bits.map rho) (eval rho position)
    (ordered_bits_boolean rho satisfied) (ordered_position rho satisfied)
  have count : bits.length = {width} := by decide
  simpa only [List.length_map, count] using result
'''
    for name in ('constantLink', 'ordered_bits_boolean', 'ordered_position', 'actual_position_bound'):
        source += '#print axioms ' + name + '\n'
    return _signature_audits(source + f'end ShielddSecurity.{ns}\n')


def membership_obligations(manifest_data, page_data, accepted_roles):
    """Current compliance gate operands; computed root is not assumed correct."""
    checked = inspect_page(manifest_data, page_data, 0, accepted_roles)
    obj = checked['metadata']; scope = obj['scope']
    require(scope in ('sender', 'receiver'), 'compliance membership scope')
    def value(ref):
        kind, item = reference(ref)
        return canonical([(0, item)]) if kind == 'native' else checked['observed'][item]
    member = checked['records'][scope, 'membership', 0]
    root = value(checked['records'][scope, 'computed-root', 0][0])
    anchor = value(member[3]); regulated = value(member[4])
    require(len(regulated) == 1 and regulated[0][1] == 1 and regulated[0][0] not in
            (0, obj['constant_copy']), 'compliance actual Boolean witness')
    return dict(checked=checked, root=root, anchor=anchor, regulated=regulated,
                difference=combine(root, anchor, -1))


def _membership_requirements(selected):
    obj = selected['checked']['metadata']; copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c, v) for c, v in lc)
    left, right = selected['regulated'], selected['difference']
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy'],
                (outline(left), outline(left)): ['regulated-Boolean']}
    products = []; squares = []
    if not right or len(right) == 1 and right[0][0] == 0:
        coefficient = right[0][1] if right else 0
        output = canonical((c, v*coefficient) for c,v in left)
        if output: required[(outline(output), ())] = ['folded-membership-zero']
    elif left == right:
        squares = [('membership-zero', outline(left), ())]
    else:
        products = [('membership-zero', outline(combine(left, right, -1)),
                     outline(combine(left, right)), None, ())]
    return required, products, squares


def extract_membership(manifest_data, page_data, stream, accepted_roles):
    selected = membership_obligations(manifest_data, page_data, accepted_roles)
    obj = selected['checked']['metadata']
    required, products, squares = _membership_requirements(selected)
    extracted = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                             required, products, squares, label='remaining-membership')
    extracted.update(metadata_sha256=selected['checked']['metadata_sha256'], membership_scope=obj['scope'],
                     scope='exact regulated Boolean and gated final-root/anchor rows only; leaf/hash/path/native/lifecycle joins open')
    return extracted


def membership_certificates(manifest_data, page_data, extracted, accepted_roles):
    selected = membership_obligations(manifest_data, page_data, accepted_roles)
    obj = selected['checked']['metadata']
    require(extracted.get('membership_scope') == obj['scope'], 'membership extraction exact scope')
    raw, rows = arithmetic.normalize_selection(extracted, obj, selected['checked']['metadata_sha256'])
    left, right = selected['regulated'], selected['difference']
    boolean = [i for i,row in rows.items() if row == (left,left)]
    require(len(boolean) == 1, 'membership actual Boolean row missing/ambiguous')
    # The existing materialization/assertion certificate infers its output only
    # from actual physical rows. Zero is a checked assertion, not an argument
    # demanding the desired value of an arbitrary source node.
    materialized = arithmetic.quotient_certificate((), left, right, rows)
    output = materialized['output']
    product = arithmetic.product_certificate(left, right, output, rows)
    assertion = None
    if output:
        reverse = canonical((c,-v) for c,v in output)
        found = [(i,row[0] == output) for i,row in rows.items() if row in ((output,()),(reverse,()))]
        require(len(found) == 1, 'membership actual zero assertion missing/ambiguous')
        assertion = found[0]
    copy = obj['constant_copy']; links = [i for i,row in raw.items() if row == (canonical([(0,1),(copy,-1)]),())]
    used = set(boolean) | set(product['rows']) | ({assertion[0]} if assertion else set())
    require(len(links) == 1 and used | set(links) == set(raw), 'membership exact physical-row coverage')
    selected.update(raw=raw, product=product, output=output, assertion=assertion)
    return selected


def generate_membership(manifest_data, page_data, extracted, accepted_roles):
    from .generate_hash_round import linear, signed, _signature_audits
    selected = membership_certificates(manifest_data, page_data, extracted, accepted_roles)
    obj = selected['checked']['metadata']; copy = obj['constant_copy']; c = selected['product']
    ns = 'RuntimeTransfer' + obj['scope'].capitalize() + 'MembershipGate'
    datum = ('.product ' + linear(c['auxiliary']) if c['kind'] == 'product' else '.square' if c['kind'] == 'square'
             else ('.foldedLeft ' if c['kind'] == 'folded_left' else '.foldedRight ') + f'({signed(c["coefficient"])} : Int)')
    first, second = ('difference','regulated') if c.get('swapped') else ('regulated','difference')
    source = f'''import ShielddSecurity.ScalarRows
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 300000
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {list(selected['raw'])}
def rawRows : List Row := [''' + ',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩'for a,b in selected['raw'].values()) + f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def root : Linear := {linear(selected['root'])}
def anchor : Linear := {linear(selected['anchor'])}
def regulated : Linear := {linear(selected['regulated'])}
def difference : Linear := {linear(selected['difference'])}
def productOutput : Linear := {linear(selected['output'])}
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
theorem fourNonzero {{F : Type}} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
theorem regulated_boolean {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho regulated = 0 ∨ eval rho regulated = 1 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  exact boolean_sound _ (Compiler.checked_row_sound rho rows ⟨regulated,regulated⟩ normalized (by decide))
theorem gated_membership {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho regulated * (eval rho root - eval rho anchor) = 0 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product := ScalarRows.checked_product_sound rho one (fourNonzero (F := F)) rows normalized
    {first} {second} productOutput ({datum}) (by decide)
  have diff := Compiler.canonical_equal rho difference (Compiler.subtract root anchor) (by decide)
  rw [Compiler.eval_subtract] at diff
'''
    if selected['assertion']:
        a,b=('productOutput','[]') if selected['assertion'][1] else ('[]','productOutput')
        source += f'  have zero : eval rho productOutput = 0 := by\n    have equation := Compiler.checked_assertion_sound rho rows {a} {b} normalized (by decide)\n'
        source += '    simpa only [eval] using '+('equation.symm' if not selected['assertion'][1] else 'equation')+'\n'
    else: source += '  have zero : eval rho productOutput = 0 := by simp only [productOutput,eval]\n'
    source += '''  rw [zero] at product
  simpa only [diff,mul_comm] using product.symm
theorem active_membership {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows)
    (active : eval rho regulated ≠ 0) : eval rho root = eval rho anchor := by
  have zero := gated_membership rho one satisfied
  exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left active)
'''
    for name in ('constantLink','fourNonzero','regulated_boolean','gated_membership','active_membership'):
        source += '#print axioms '+name+'\n'
    return _signature_audits(source + f'end ShielddSecurity.{ns}\n')
