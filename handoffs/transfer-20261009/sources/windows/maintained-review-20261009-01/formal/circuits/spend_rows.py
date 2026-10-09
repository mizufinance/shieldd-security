"""Select the precise spend/history slice from actual Transfer Pari rows.

Full-relation membership and the source-index/compiled-expression observation
are explicit reviewed extraction boundaries. Selection is not itself a proof.
Hash outputs below stay opaque linear expressions until their gadgets are proved.
"""
import re
from generate import P


def select(export):
    if export.get('subject') != 'actual Transfer spend and statement observations':
        raise ValueError('wrong spend export subject')
    if export.get('scalar_encoding') != 'canonical-big-endian-32' or int(export.get('modulus_minus_one', '0'), 16) != P - 1:
        raise ValueError('wrong spend scalar field')
    if not re.fullmatch('[0-9a-f]{64}', export.get('relation_digest', '')):
        raise ValueError('missing full relation identity')
    domain, count = export['domain_size'], export['row_count']
    if type(domain) is not int or domain < 4 or domain & (domain - 1) or type(count) is not int or not 0 < count <= domain:
        raise ValueError('invalid relation dimensions')
    if export['public_inputs'] != 1 or export['committed_blocks'] != [1]:
        raise ValueError('changed Transfer input layout')
    if export['literals'] != [{'kind': 'native', 'label': 'spend0.dummy', 'value': '0' * 64}]:
        raise ValueError('required input is not the observed literal zero')
    if export['padding'] != [{'domain': 22, 'hash_slot': 1, 'slot': 1}]:
        raise ValueError('wrong optional padding domain/slot')

    def linear(terms):
        values = {}
        for column, coefficient in terms:
            values[column] = (values.get(column, 0) + coefficient) % P
        return tuple((i, c if c <= P // 2 else c - P) for i, c in sorted(values.items()) if c)

    def parse(terms):
        result = []
        previous = -1
        for column, encoded in terms:
            if type(column) is not int or not previous < column < domain:
                raise ValueError('invalid/noncanonical expression columns')
            if not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded):
                raise ValueError('noncanonical scalar encoding')
            coefficient = int(encoded, 16)
            if not 0 < coefficient < P:
                raise ValueError('invalid/noncanonical coefficient')
            result.append((column, coefficient))
            previous = column
        return linear(result)

    observations = {}
    expression_order = []
    for item in export['expressions']:
        label = item['label']
        if label in observations or item['kind'] != 'linear':
            raise ValueError('duplicate or unsupported spend observation')
        source = item['source']
        if source['kind'] not in ['constant', 'witness', 'node'] or type(source['index']) is not int or source['index'] < 0:
            raise ValueError('invalid source identity')
        observations[label] = {'source': source, 'linear': parse(item['terms'])}
        expression_order.append(label)

    def expr(label):
        if label not in observations:
            raise ValueError(f'missing source expression {label}')
        return observations[label]['linear']

    def column(label):
        value = expr(label)
        source = observations[label]['source']
        if len(value) != 1 or value[0][1] != 1 or not 3 <= value[0][0] < domain or source['kind'] != 'witness' or source['index'] + 3 != value[0][0]:
            raise ValueError(f'{label}: expected actual private witness column')
        return value[0][0]

    # Caller joins refer to identical retained source handles, not merely equal
    # honest test values. Their semantic interpretation remains the observer TCB.
    for slot in [0, 1]:
        for role, field in [('anchor', 2), ('floor', 12), ('nullifier', 17 + slot * 2), ('history', 18 + slot * 2)]:
            if observations[f'spend{slot}.{role}'] != observations[f'statement.{field}']:
                raise ValueError(f'spend{slot}.{role}: wrong actual statement slot/source binding')
    if observations['spend0.floor'] != observations['spend1.floor']:
        raise ValueError('caller recent floor differs between inputs')
    expected_statements = {f'statement.{i}' for i in range(67)}
    if {name for name in observations if name.startswith('statement.')} != expected_statements:
        raise ValueError('incomplete statement observation')

    table, indices = {}, {}
    for row in export['rows']:
        index = row['index']
        if type(index) is not int or not 0 <= index < count:
            raise ValueError('invalid original row index')
        key = (parse(row['a']), parse(row['b']))
        if index in indices and indices[index] != key:
            raise ValueError('contradictory original row index')
        indices[index] = key
        table.setdefault(key, row)

    blocks = {}

    def get(a, b=()):
        key = (linear(a), linear(b))
        if key not in table:
            raise ValueError(f'missing exact spend row {key}')
        return table[key]

    def zero(a):
        # (a)^2=0 and (-a)^2=0 have the same field consequence. Record which
        # actual sign was present; the generator must prove its normalization.
        key = linear(a)
        matches = [table[(sign, ())] for sign in {key, linear([(i, -c) for i, c in key])} if (sign, ()) in table]
        if len(matches) != 1:
            raise ValueError('missing or ambiguous zero row')
        return matches[0]

    constants = [(a, row) for (a, b), row in table.items() if not b and len(a) == 2 and a[0] == (0, 1) and a[1][1] == -1]
    if len(constants) != 1 or constants[0][0][1][0] < 3:
        raise ValueError('missing unique outlined constant-one boundary')
    outline = constants[0][0][1][0]
    blocks['constant'] = [constants[0][1]]
    groups, all_bits = {}, []
    for group in export['bit_groups']:
        slot, role, start, width = (group[k] for k in ['slot', 'role', 'start', 'width'])
        if slot not in [0, 1] or role not in ['amount', 'position', 'floor', 'difference'] or type(start) is not int:
            raise ValueError('invalid range group')
        if width != (128 if role == 'amount' else 48):
            raise ValueError('wrong unconditional range width')
        name = f'spend{slot}.{role}'
        if name in groups or expression_order[start:start + width] != [f'{name}.bit{i}' for i in range(width)]:
            raise ValueError('aliased or incorrectly located bit group')
        bits = [column(f'{name}.bit{i}') for i in range(width)]
        groups[name] = bits
        all_bits.extend(bits)
        reconstruction = [(column(name), -1)] + [(bit, 2**i) for i, bit in enumerate(bits)]
        blocks[name] = [get([(bit, 1)], [(bit, 1)]) for bit in bits] + [zero(reconstruction)]
    if len(groups) != 8 or len(set(all_bits)) != len(all_bits):
        raise ValueError('missing or overlapping decomposition groups')

    support = {i for item in observations.values() for i, _ in item['linear']}
    if outline in support or any(bit in {column(f'spend{s}.{r}') for s in [0, 1] for r in ['history', 'amount', 'nullifier', 'position', 'floor', 'anchor', 'borrow', 'difference']} for bit in all_bits):
        raise ValueError('range/semantic/constant role alias')
    semantic_roles = [f'spend{s}.{r}' for s in [0, 1]
                      for r in ['history', 'amount', 'nullifier', 'position', 'floor', 'anchor', 'borrow', 'difference']]
    semantic_roles.append('spend1.dummy')
    aliases = {}
    for role in semantic_roles:
        aliases.setdefault(column(role), []).append(role)
    allowed_aliases = [{'spend0.floor', 'spend1.floor'}, {'spend0.anchor', 'spend1.anchor'}]
    if any(len(roles) > 1 and set(roles) not in allowed_aliases for roles in aliases.values()):
        raise ValueError('unexpected semantic role alias')
    # Explicit support ownership for composition. The extension preserves these
    # opaque outputs; it never synthesizes a hash preimage or overwrites them.
    hash_roles = ['spend0.real_nullifier', 'spend0.computed_root', 'spend1.real_nullifier',
                  'spend1.computed_root', 'spend1.synthetic_nullifier']
    occupied = set(all_bits) | set(aliases) | {0, 1, 2, outline}
    for role in hash_roles:
        terms = expr(role)
        columns = {i for i, _ in terms}
        if not terms or observations[role]['source']['kind'] != 'node' or columns & occupied:
            raise ValueError('opaque hash expression has aliased or missing support')
        occupied.update(columns)
    auxiliaries = set()

    def product(name, x, y, result=None):
        minus = linear(list(x) + [(i, -c) for i, c in y])
        matches = [(b, row) for (a, b), row in table.items() if a == minus and len(b) == 1 and b[0][1] == 1]
        if len(matches) != 1:
            raise ValueError(f'{name}: missing or ambiguous product difference square')
        (d, _), first = matches[0][0][0], matches[0][1]
        plus = linear(list(x) + list(y))
        matches = [(b, row) for (a, b), row in table.items() if a == plus and len(b) == 2 and dict(b).get(d) == 1]
        if len(matches) != 1:
            raise ValueError(f'{name}: missing or ambiguous product sum square')
        b, second = matches[0]
        outputs = [(i, c) for i, c in b if i != d]
        if len(outputs) != 1 or outputs[0][1] != 4:
            raise ValueError('wrong multiplication scaling')
        o = outputs[0][0]
        if d == o or any(not 3 <= i < domain or i in support or i == outline or i in auxiliaries for i in [d, o]):
            raise ValueError('invalid/shared multiplication auxiliary')
        auxiliaries.update([d, o])
        target = [] if result is None else list(result)
        blocks[name] = [first, second, zero([(o, 1)] + [(i, -c) for i, c in target])]
        return {'difference': d, 'output': o, 'x': list(x), 'y': list(y), 'result': target}

    for slot in [0, 1]:
        label = f'spend{slot}'
        borrow, difference, history = [column(f'{label}.{r}') for r in ['borrow', 'difference', 'history']]
        blocks[f'{label}.booleans'] = [get([(i, 1)], [(i, 1)]) for i in [borrow, history]]
        equation = ([(bit, 2**i) for i, bit in enumerate(groups[f'{label}.position'])]
                    + [(bit, -2**i) for i, bit in enumerate(groups[f'{label}.floor'])]
                    + [(borrow, 2**48), (difference, -1)])
        blocks[f'{label}.comparison'] = [zero(equation)]
    blocks['required.nullifier'] = [zero(list(expr('spend0.real_nullifier')) + [(column('spend0.nullifier'), -1)])]
    blocks['required.anchor'] = [zero(list(expr('spend0.computed_root')) + [(column('spend0.anchor'), -1)])]
    blocks['required.history'] = [zero([(column('spend0.borrow'), 1), (column('spend0.history'), -1)])]
    dummy = column('spend1.dummy')
    blocks['optional.boolean'] = [get([(dummy, 1)], [(dummy, 1)])]
    real = [(outline, 1), (dummy, -1)]
    real_nf = list(expr('spend1.real_nullifier'))
    gates = {
        'optional.nullifier': product('optional.nullifier', [(dummy, 1)],
            linear(list(expr('spend1.synthetic_nullifier')) + [(i, -c) for i, c in real_nf]),
            linear([(column('spend1.nullifier'), 1)] + [(i, -c) for i, c in real_nf])),
        'optional.anchor': product('optional.anchor', real,
            linear(list(expr('spend1.computed_root')) + [(column('spend1.anchor'), -1)])),
        'optional.amount': product('optional.amount', [(dummy, 1)], [(column('spend1.amount'), 1)]),
        'optional.history': product('optional.history', real, [(column('spend1.borrow'), 1)], [(column('spend1.history'), 1)]),
    }
    extension_columns = sorted(auxiliaries | {
        column(f'spend{s}.{role}') for s in [0, 1] for role in ['borrow', 'difference']
    } | set(groups['spend0.difference']) | set(groups['spend1.difference']))
    preserved_roles = [role for role in observations
                       if not role.startswith(('spend0.borrow', 'spend1.borrow',
                                               'spend0.difference', 'spend1.difference'))]
    if any(set(i for i, _ in expr(role)) & set(extension_columns) for role in preserved_roles):
        raise ValueError('local extension would overwrite a retained source expression')
    return {'digest': export['relation_digest'], 'domain': domain, 'outline': outline,
            'observations': observations, 'bits': groups, 'blocks': blocks, 'gates': gates,
            'opaque_hash_roles': hash_roles,
            'extension_columns': extension_columns,
            'selected_indices': sorted({r['index'] for block in blocks.values() for r in block})}
