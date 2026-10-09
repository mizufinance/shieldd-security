"""Actual cofactor source boundaries, ahead of compiled-row instantiation.

This closes the finite source cones against the independent addition equations.
It does not certify inverse witnesses or a subgroup: those require the original
inverse/assertion rows and Compiler/GroupWindows kernel certificates.
"""
import re

try:
    from .poseidon_graph import P, match_export, match_source
    from .hash_rows import canonical, scaled
except ImportError:
    from poseidon_graph import P, match_export, match_source
    from hash_rows import canonical, scaled

D = -10240 * pow(10241, -1, P) % P


def expected(role):
    """Original complete Edwards formulas with explicit native/circuit leaves.

    Circuit constants preserve operand order; only Native operands are moved
    left by Var.merge. This distinction matters for the actual coefficient d.
    No witness evaluation is used to build or match these equations.
    """
    nodes, native = [], []

    def put(value, is_native=False):
        nodes.append(value)
        native.append(is_native)
        return len(nodes) - 1

    def const(value, is_native=False):
        return put({'kind': 'constant', 'value': value % P}, is_native)

    def op(kind, left, right):
        a, b = nodes[left], nodes[right]
        if a['kind'] == b['kind'] == 'constant':
            return const(a['value'] + b['value'] if kind == 'add' else a['value'] * b['value'],
                         native[left] and native[right])
        if native[right] and not native[left]:
            left, right = right, left
        return put({'kind': kind, 'left': left, 'right': right})

    def sub(left, right):
        return op('add', left, op('mul', const(-1), right))

    if role not in ('curve.left', 'curve.right', 'denominator', 'x', 'y'):
        raise ValueError('unknown group formula')
    arity = 3 if role in ('x', 'y') else 2
    inputs = [put({'kind': 'input', 'slot': i}) for i in range(arity)]
    x, y = inputs[:2]
    xx, yy = op('mul', x, x), op('mul', y, y)
    d, one = const(D), const(1, True)
    if role == 'curve.left':
        output = sub(yy, xx)
    elif role == 'curve.right':
        output = op('add', one, op('mul', op('mul', d, xx), yy))
    else:
        dt = op('mul', op('mul', xx, yy), d)
        plus, minus = op('add', one, dt), sub(one, dt)
        if role == 'denominator':
            output = op('mul', plus, minus)
        elif role == 'x':
            cross = op('add', op('mul', x, y), op('mul', y, x))
            output = op('mul', op('mul', cross, minus), inputs[2])
        else:
            output = op('mul', op('mul', op('add', yy, xx), plus), inputs[2])
    return {'arity': arity, 'nodes': nodes, 'output': output}


def match_group(export, parameter_root):
    hashes = match_export(export, parameter_root)
    if export.get('ordinary_constructor_checked') is not True:
        raise ValueError('missing actual ordinary-constructor parity')
    group = export.get('group_subgroup')
    if (not isinstance(group, dict) or set(group) != {'subject', 'coefficient_d', 'roles', 'cones'}
            or group['subject'] != 'actual action authorization key cofactor constraint'
            or group['coefficient_d'] != f'{D:064x}'):
        raise ValueError('wrong group scope/parameter')
    roles = group['roles']
    expected_roles = {'coefficient_d', 'point.x', 'point.y', 'point.inverse',
                      'preimage.x', 'preimage.y', 'curve.left', 'curve.right'}
    expected_roles.update(f'double{i}.{name}' for i in range(3)
                          for name in ('before.x', 'before.y', 'after.x', 'after.y', 'inverse', 'denominator'))
    observations = {item['source']: item for item in export['expressions']}
    if not isinstance(roles, dict) or set(roles) != expected_roles:
        raise ValueError('missing/extra group role')
    if any(not isinstance(identity, str) or identity not in observations for identity in roles.values()):
        raise ValueError('unobserved group role')
    for axis in ('x', 'y'):
        if roles[f'point.{axis}'] != export['ownership'][f'action.ak.{axis}']:
            raise ValueError('cofactor point differs from actual action/IVK key')
        if roles[f'double0.before.{axis}'] != roles[f'preimage.{axis}']:
            raise ValueError('first double does not consume actual preimage')
        for i in range(1, 3):
            if roles[f'double{i}.before.{axis}'] != roles[f'double{i - 1}.after.{axis}']:
                raise ValueError('cofactor doubling source chain disconnected')
    witnesses = [roles[name] for name in ('point.x', 'point.y', 'preimage.x', 'preimage.y', 'point.inverse')]
    witnesses.extend(roles[f'double{i}.inverse'] for i in range(3))
    if len(set(witnesses)) != len(witnesses) or any(not re.fullmatch(r'w(0|[1-9][0-9]*)', item) for item in witnesses):
        raise ValueError('unsupported aliased/non-witness group inputs')
    assertions = {(item['left'], item['right']) for item in export['touching_source_assertions']}
    required = [(roles['curve.left'], roles['curve.right'])]
    required.extend((roles[f'double2.after.{axis}'], roles[f'point.{axis}']) for axis in ('x', 'y'))
    if any(pair not in assertions and pair[::-1] not in assertions for pair in required):
        raise ValueError('missing actual curve/cofactor source assertion')
    cone_roles = ['curve.left', 'curve.right'] + [f'double{i}.{name}' for i in range(3)
                                                for name in ('denominator', 'after.x', 'after.y')]
    cones = group['cones']
    if not isinstance(cones, list) or len(cones) != len(cone_roles):
        raise ValueError('missing/extra group cone')
    shared = {identity: value for call in hashes for identity, value in call['source'].items()}
    result = []
    for cone, role in zip(cones, cone_roles):
        if not isinstance(cone, dict) or set(cone) != {'role', 'inputs', 'output', 'source'} or cone['role'] != role:
            raise ValueError('wrong ordered group cone')
        if role.startswith('curve.'):
            formula, input_roles = role, ['preimage.x', 'preimage.y']
        else:
            prefix, tail = role.split('.', 1)
            formula = tail.removeprefix('after.')
            input_roles = [f'{prefix}.before.x', f'{prefix}.before.y']
            if formula != 'denominator':
                input_roles.append(f'{prefix}.inverse')
        if cone['inputs'] != [roles[name] for name in input_roles] or cone['output'] != roles[role]:
            raise ValueError('wrong group cone endpoint/slot')
        if not isinstance(cone['source'], dict):
            raise ValueError('missing group source graph')
        source = {}
        for identity, item in cone['source'].items():
            value = dict(item)
            if value.get('kind') == 'constant':
                encoded = value.get('value')
                if not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded) or int(encoded, 16) >= P:
                    raise ValueError('noncanonical group source constant')
                value['value'] = int(encoded, 16)
            if identity not in observations or identity in shared and shared[identity] != value:
                raise ValueError('unobserved/contradictory shared group source')
            source[identity] = shared[identity] = value
        graph = expected(formula)
        pairs = match_source(graph, source, cone['inputs'], cone['output'])
        result.append({'role': role, 'graph': graph, 'source': source, 'pairs': pairs,
                       'inputs': cone['inputs'], 'output': cone['output']})
    if shared.get(roles['coefficient_d']) != {'kind': 'constant', 'value': D}:
        raise ValueError('wrong actual coefficient source identity')
    return {'roles': roles, 'cones': result, 'assertions': required,
            'scope': 'source correspondence only; inverse/assertion and operation row certificates pending'}


def select_boundary_rows(export, parameter_root):
    """Select real inverse and assertion rows, never infer them from handles.

    The existing scalar ingress validates the common relation/layout, canonical
    LCs and unique row indices. Its row conclusions are not assumed here. The
    original raw rows and outlined-one link remain required kernel premises.
    Arithmetic operations within each matched group cone are a separate next
    certificate; these boundary rows alone do not prove curve/subgroup meaning.
    """
    from scalar_rows import select as scalar_select
    from terminal_rows import match_terminal
    checked = scalar_select(export, parameter_root)
    matched = match_group(export, parameter_root)
    outline, link = checked['outline'], checked['constant_link']

    def parse(terms):
        # Every raw coefficient and dimension has already passed strict scalar
        # ingress; retain exact emitted rows rather than rewriting evidence.
        return tuple((column, int(encoded, 16)) for column, encoded in terms)

    raw = {row['index']: (parse(row['a']), parse(row['b'])) for row in export['rows']}
    observations = {item['source']: (item['kind'], parse(item['terms'])) for item in export['expressions']}
    table, squared, used = {}, {}, {link}
    for index, (a, b) in sorted(raw.items()):
        a, b = (canonical((0 if c == outline else c, v) for c, v in terms) for terms in (a, b))
        table.setdefault((a, b), index)
        squared.setdefault(a, []).append((b, index))

    def term(role):
        kind, value = observations[matched['roles'][role]]
        if kind != 'linear':
            raise ValueError('unsupported nonlinear group boundary')
        return value

    def equal(left, right):
        delta = canonical(left + scaled(right, -1))
        for value in (delta, scaled(delta, -1)):
            if (value, ()) in table:
                index = table[(value, ())]
                used.add(index)
                return {'row': index, 'expression': value}
        raise ValueError('missing actual group equality row')

    def inverse(left, right, role, source_inputs):
        # Neither inverse may be an alias of its operand. Constant/native
        # inverses and unsupported fused shapes are rejected in this slice.
        if not left or not right or left == right or all(c == 0 for c, _ in left + right):
            raise ValueError('unsupported group inverse boundary')
        matched = match_terminal(export, role, source_inputs, False, 1, observations)
        for x, y in ((left, right), (right, left)):
            minus, plus = canonical(x + scaled(y, -1)), canonical(x + y)
            for auxiliary, first in squared.get(minus, []):
                pair = (plus, canonical(auxiliary + scaled(matched['output'], 4)))
                if pair in table:
                    second = table[pair]
                    used.update((first, second))
                    assertion = equal(matched['output'], matched['target'])
                    return {'left': x, 'right': y, 'output': matched['output'],
                            'target': matched['target'], 'assertion': assertion,
                            'auxiliary': auxiliary, 'rows': [first, second]}
        raise ValueError('missing actual denominator/nonidentity inverse rows')

    witness_roles = ['point.x', 'point.y', 'preimage.x', 'preimage.y', 'point.inverse']
    witness_roles.extend(f'double{i}.inverse' for i in range(3))
    for role in witness_roles:
        identity = matched['roles'][role]
        if term(role) != ((int(identity[1:]) + 3, 1),):
            raise ValueError('wrong original group witness column projection')
    if term('coefficient_d') != ((0, D),):
        raise ValueError('wrong group coefficient linear observation')
    point_inverse = inverse(term('point.x'), term('point.inverse'), 'group.point_inverse',
                            [matched['roles']['point.x'], matched['roles']['point.inverse']])
    inverses = [inverse(term(f'double{i}.denominator'), term(f'double{i}.inverse'),
                        f'group.double{i}_inverse', [matched['roles'][f'double{i}.denominator'],
                        matched['roles'][f'double{i}.inverse']]) for i in range(3)]
    curve = equal(term('curve.left'), term('curve.right'))
    final = [equal(term(f'double2.after.{axis}'), term(f'point.{axis}')) for axis in ('x', 'y')]
    return {'scope': 'actual group boundary row selection; kernel and arithmetic-cone certificates required',
            'source': matched, 'outline': outline, 'constant_link': link,
            'roles': {role: term(role) for role in matched['roles']}, 'point_inverse': point_inverse,
            'double_inverses': inverses, 'curve_assertion': curve, 'cofactor_assertions': final,
            'rows': {index: raw[index] for index in sorted(used)}}
