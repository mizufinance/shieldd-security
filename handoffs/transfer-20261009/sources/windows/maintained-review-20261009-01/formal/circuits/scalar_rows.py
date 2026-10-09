"""Select the actual IVK reduction equations; selection is not a Lean proof.

Reuses the source-cone matcher and LC arithmetic from the hash lane. It refuses
unknown roles, malformed/aliased bit layouts, changed comparator source steps,
missing bounds, or missing arithmetic rows. No honest reducer values are read.
"""
import re

from hash_rows import canonical, scaled
from poseidon_graph import P, match_export, match_source
from terminal_rows import match_terminal

ORDER = 6554484396890773809930967563523245729705921265872317281365359162392183254199


def expected_step(right, initial):
    if type(right) is not int or right not in (0, 1) or type(initial) is not bool:
        raise ValueError('unsupported comparator bit/initial state')
    nodes = []

    def put(node):
        nodes.append(node)
        return len(nodes) - 1

    def const(value):
        return put({'kind': 'constant', 'value': value % P})

    def op(kind, left, right):
        a, b = nodes[left], nodes[right]
        if a['kind'] == b['kind'] == 'constant':
            return const(a['value'] + b['value'] if kind == 'add' else a['value'] * b['value'])
        if b['kind'] == 'constant':
            left, right = right, left
        return put({'kind': kind, 'left': left, 'right': right})

    def minus(left, right):
        return op('add', left, op('mul', const(-1), right))

    left = put({'kind': 'input', 'slot': 0})
    lower = const(1) if initial else put({'kind': 'input', 'slot': 1})
    x, y = minus(const(1), left), const(right)
    both = op('mul', x, y)
    unequal = minus(op('add', x, y), op('add', both, both))
    output = op('add', both, op('mul', lower, unequal))
    return {'arity': 1 if initial else 2, 'nodes': nodes, 'output': output}


def select(export, parameter_root, comparison=None):
    if comparison is not None and comparison not in ('quotient', 'remainder', 'last'):
        raise ValueError('unknown scalar selection scope')
    hashes = match_export(export, parameter_root)
    if export.get('ordinary_constructor_checked') is not True:
        raise ValueError('missing actual normal-constructor parity')
    scalar = export.get('scalar_reduction')
    if not isinstance(scalar, dict) or set(scalar) != {'subject', 'roles', 'comparisons'} or scalar['subject'] != 'actual IVK canonical reduction':
        raise ValueError('missing exact scalar observation scope')
    widths = {'quotient': 4, 'remainder': 252, 'last': 252}
    maxima = {'quotient': 8, 'remainder': ORDER - 1, 'last': P - 1 - 8 * ORDER}
    expected = {'value', 'quotient', 'remainder', 'ivk', 'ivk_inverse'}
    expected.update(f'{name}.bit{i}' for name, width in widths.items() if name != 'last' for i in range(width))
    expected.update(f'{name}.comparison{i}' for name, width in widths.items() for i in range(width))
    roles = scalar['roles']
    if not isinstance(roles, dict) or set(roles) != expected:
        raise ValueError('missing/extra scalar role')
    if roles['value'] != hashes[0]['output']:
        raise ValueError('reduction input is not actual IVK hash output')
    domain, count = export['domain_size'], export['row_count']
    if (type(domain) is not int or domain < 4 or domain & (domain - 1) or type(count) is not int
            or not 0 < count <= domain or type(export['public_inputs']) is not int or export['public_inputs'] != 1
            or not isinstance(export['committed_blocks'], list) or len(export['committed_blocks']) != 1
            or type(export['committed_blocks'][0]) is not int or export['committed_blocks'][0] != 1
            or not isinstance(export['relation_digest'], str)
            or not re.fullmatch('[0-9a-f]{64}', export['relation_digest'])
            or export.get('ordinary_relation_digest') != export['relation_digest']
            or export.get('ordinary_observed_identity_equal') is not True):
        raise ValueError('wrong scalar relation dimensions/layout')

    def parse(terms):
        result, previous = [], -1
        for column, encoded in terms:
            if type(column) is not int or not previous < column < domain or not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded):
                raise ValueError('noncanonical scalar LC')
            coefficient = int(encoded, 16)
            if not 0 < coefficient < P:
                raise ValueError('noncanonical scalar coefficient')
            result.append((column, coefficient))
            previous = column
        return tuple(result)

    observations = {item['source']: (item['kind'], parse(item['terms'])) for item in export['expressions']}
    if any(not isinstance(ref, str) or ref not in observations for ref in roles.values()):
        raise ValueError('unobserved scalar role')
    raw = {}
    for row in export['rows']:
        index = row['index']
        if type(index) is not int or not 0 <= index < count or index in raw:
            raise ValueError('duplicate/invalid scalar row')
        raw[index] = (parse(row['a']), parse(row['b']))
    links = [(i, a[1][0]) for i, (a, b) in raw.items() if not b and len(a) == 2 and a[0] == (0, 1) and a[1][1] == P - 1 and a[1][0] >= 3]
    if len(links) != 1:
        raise ValueError('missing/ambiguous constant-one link')
    link, outline = links[0]
    if any(c == outline for _, terms in observations.values() for c, _ in terms):
        raise ValueError('pre-outline observation uses private copy')
    table, squared, used = {}, {}, {link}
    for i, (a, b) in raw.items():
        a, b = (canonical((0 if c == outline else c, value) for c, value in terms) for terms in (a, b))
        table.setdefault((a, b), i)
        squared.setdefault(a, []).append((b, i))

    def term(role):
        kind, value = observations[roles[role]]
        if kind != 'linear':
            raise ValueError('unsupported nonlinear scalar boundary')
        return value

    def zero(left, right=()):
        value = canonical(left + scaled(right, -1))
        for expression in (value, scaled(value, -1)):
            if (expression, ()) in table:
                index = table[(expression, ())]
                used.add(index)
                return {'row': index, 'expression': expression}
        raise ValueError('missing scalar equality/assertion row')

    def product(left, right, output):
        for name, value, other in [('left', left, right), ('right', right, left)]:
            if not value or len(value) == 1 and value[0][0] == 0:
                coefficient = value[0][1] if value else 0
                if output != scaled(other, coefficient):
                    raise ValueError('incorrect folded comparator product')
                return {'kind': 'constant', 'side': name, 'coefficient': coefficient}
        if left == right and (left, output) in table:
            index = table[(left, output)]
            used.add(index)
            return {'kind': 'square', 'rows': [index]}
        minus, plus = canonical(left + scaled(right, -1)), canonical(left + right)
        for auxiliary, i in sorted(squared.get(minus, []), key=lambda item: item[1]):
            pair = (plus, canonical(auxiliary + scaled(output, 4)))
            if pair in table:
                used.update([i, table[pair]])
                return {'kind': 'product', 'rows': [i, table[pair]], 'auxiliary': auxiliary}
        raise ValueError('missing scalar product rows')

    bits, range_rows = {}, {}
    all_bits = []
    for name in ('quotient', 'remainder'):
        identities = [roles[f'{name}.bit{i}'] for i in range(widths[name])]
        all_bits.extend(identities)
        values = [term(f'{name}.bit{i}') for i in range(widths[name])]
        for identity, value in zip(identities, values):
            if not re.fullmatch('w[0-9]+', identity) or value != ((int(identity[1:]) + 3, 1),):
                raise ValueError('unsupported bit witness projection')
            if (value, value) not in table:
                raise ValueError('missing Boolean bit row')
            used.add(table[(value, value)])
        bits[name] = values
        reconstruction = canonical(item for i, value in enumerate(values) for item in scaled(value, 2 ** i))
        range_rows[name] = zero(reconstruction, term(name))
    if len(set(all_bits)) != 256:
        raise ValueError('aliased reduction bit witnesses')
    witness_roles = [roles[name] for name in ('quotient', 'remainder', 'ivk_inverse')]
    if len(set(all_bits + witness_roles)) != 259:
        raise ValueError('aliased reduction value/bit/inverse witnesses')
    for name in ('quotient', 'remainder', 'ivk_inverse'):
        identity = roles[name]
        if not re.fullmatch('w[0-9]+', identity) or term(name) != ((int(identity[1:]) + 3, 1),):
            raise ValueError('unsupported reduction witness projection')
    if term('ivk') != canonical(item for i, value in enumerate(bits['remainder']) for item in scaled(value, 2 ** i)):
        raise ValueError('IVK does not use the actual reduced bits')
    if len(scalar['comparisons']) != sum(widths.values()):
        raise ValueError('missing/extra comparison step')
    known_source = {identity: node for call in hashes for identity, node in call['source'].items()}
    steps, cursor = [], 0
    for name, width in widths.items():
        bit_name = 'remainder' if name == 'last' else name
        for i in range(width):
            item = scalar['comparisons'][cursor]
            cursor += 1
            lower = None if i == 0 else roles[f'{name}.comparison{i-1}']
            right = maxima[name] >> i & 1
            if (set(item) != {'comparison', 'index', 'left', 'right_literal', 'lower', 'initial_literal', 'output', 'source'}
                    or item['comparison'] != name or type(item['index']) is not int or item['index'] != i
                    or item['left'] != roles[f'{bit_name}.bit{i}'] or type(item['right_literal']) is not int or item['right_literal'] != right
                    or item['lower'] != lower
                    or (i == 0 and (type(item['initial_literal']) is not int or item['initial_literal'] != 1))
                    or (i != 0 and item['initial_literal'] is not None)
                    or item['output'] != roles[f'{name}.comparison{i}']):
                raise ValueError('wrong comparator bit/order/prefix/bound/output')
            source = {}
            for identity, raw_node in item['source'].items():
                node = dict(raw_node)
                if node.get('kind') == 'constant':
                    encoded = node.get('value')
                    if not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded) or int(encoded, 16) >= P:
                        raise ValueError('noncanonical comparator constant')
                    node['value'] = int(encoded, 16)
                if identity in known_source and known_source[identity] != node:
                    raise ValueError('contradictory scalar/shared source identity')
                known_source[identity] = source[identity] = node
                if identity not in observations:
                    raise ValueError('unobserved comparator source')
            refs = [item['left']] + ([lower] if lower is not None else [])
            pairs = match_source(expected_step(right, i == 0), source, refs, item['output'])
            # A named development theorem certifies only its original comparator
            # rows. Full-cap/inverse assertion selection is a separate gate;
            # unrelated boundary rows are never premises of the quotient proof.
            if comparison is not None and comparison != name:
                continue
            left = bits[bit_name][i]
            before = ((0, 1),) if i == 0 else term(f'{name}.comparison{i-1}')
            after = term(f'{name}.comparison{i}')
            factor = canonical(((0, 1),) + scaled(left, -1)) if right == 0 else left
            target = after if right == 0 else canonical(after + left + ((0, P - 1),))
            steps.append({'name': name, 'index': i, 'right': right, 'before': before, 'left': left,
                          'after': after, 'pairs': pairs, 'certificate': product(before, factor, target)})
    endings = {name: zero(term(f'{name}.comparison{widths[name]-1}'), ((0, 1),))
               for name in ('quotient', 'remainder') if comparison is None or comparison == name}
    last_guard = equation = nonzero = None
    if comparison is None:
        def terminal(role, source_inputs, left, right, complement, target):
            matched = match_terminal(export, role, source_inputs, complement, target, observations)
            certificate = product(left, right, matched['output'])
            assertion = zero(matched['output'], matched['target'])
            return dict(certificate, output=matched['output'], target=matched['target'], assertion=assertion)

        last_guard = terminal('scalar.last_guard', [roles['quotient.bit3'], roles['last.comparison251']],
                              bits['quotient'][3], canonical(((0, 1),) + scaled(term('last.comparison251'), -1)), True, 0)
        equation = zero(canonical(scaled(term('quotient'), ORDER) + term('remainder')), term('value'))
        nonzero = terminal('scalar.ivk_inverse', [roles['ivk_inverse'], roles['ivk']],
                          term('ivk_inverse'), term('ivk'), False, 1)
    return {'scope': 'selected IVK reduction rows only; kernel instantiation required',
            'outline': outline, 'constant_link': link, 'roles': {role: term(role) for role in roles},
            'bits': bits, 'range_rows': range_rows, 'steps': steps, 'endings': endings,
            'last_guard': last_guard, 'equation': equation, 'nonzero': nonzero,
            'rows': {i: raw[i] for i in sorted(used)}}
