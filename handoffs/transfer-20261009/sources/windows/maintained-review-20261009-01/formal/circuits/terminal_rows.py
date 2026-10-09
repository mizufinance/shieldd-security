"""Strict original terminal product/source/assertion joins for scalar/group.

Metadata selection is an explicit extraction boundary, not a row proof. Callers
must separately certify original product rows for the observed output AND its
original equality row. No satisfying output or native witness value is read.
"""
import re

from hash_rows import canonical, scaled
from poseidon_graph import P, match_source


def expected(complement, swap_product=False, swap_add=False, swap_negative=False):
    nodes = [{'kind': 'input', 'slot': 0}, {'kind': 'input', 'slot': 1}]
    if complement:
        nodes += [{'kind': 'constant', 'value': 1},
                  {'kind': 'constant', 'value': P - 1}]
        a, b = (1, 3) if swap_negative else (3, 1)
        nodes.append({'kind': 'mul', 'left': a, 'right': b})
        a, b = (4, 2) if swap_add else (2, 4)
        nodes.append({'kind': 'add', 'left': a, 'right': b})
        factor = 5
    else:
        factor = 1
    a, b = (factor, 0) if swap_product else (0, factor)
    nodes.append({'kind': 'mul', 'left': a, 'right': b})
    return {'arity': 2, 'nodes': nodes, 'output': len(nodes) - 1}


def match_terminal(export, role, inputs, complement, target, observations):
    if type(complement) is not bool or type(target) is not int or target not in (0, 1):
        raise ValueError('unsupported terminal expectation')
    if export.get('ordinary_observed_full_ordered_equal') is not True:
        raise ValueError('missing complete ordered terminal relation parity')
    descriptors = export.get('terminal_products')
    roles = ['scalar.last_guard', 'scalar.ivk_inverse']
    if export.get('group_subgroup') is not None:
        roles += ['group.point_inverse'] + [f'group.double{i}_inverse' for i in range(3)]
    if (not isinstance(descriptors, list) or len(descriptors) != len(roles)
            or any(not isinstance(item, dict) or item.get('role') != name
                   for item, name in zip(descriptors, roles)) or role not in roles):
        raise ValueError('missing/extra/reordered original terminal roles')
    item = descriptors[roles.index(role)]
    if (set(item) != {'role', 'inputs', 'complement_right', 'target', 'product',
                     'asserted_equal', 'assertion_index', 'source'}
            or item['inputs'] != inputs or type(item['complement_right']) is not bool
            or item['complement_right'] != complement or item['target'] != f'{target:064x}'
            or not isinstance(item['product'], str) or not re.fullmatch('n(0|[1-9][0-9]*)', item['product'])
            or not isinstance(item['asserted_equal'], str)
            or not re.fullmatch('c(0|[1-9][0-9]*)', item['asserted_equal'])
            or type(item['assertion_index']) is not int
            or not 0 <= item['assertion_index'] < export['source_assertion_count']
            or not isinstance(item['source'], dict)):
        raise ValueError('wrong original terminal descriptor')
    assertions = [entry for entry in export['touching_source_assertions']
                  if entry['index'] == item['assertion_index']]
    if (len(assertions) != 1 or {assertions[0]['left'], assertions[0]['right']} !=
            {item['product'], item['asserted_equal']}):
        raise ValueError('terminal output lacks exact original source assertion')
    source = {}
    for identity, raw in item['source'].items():
        node = dict(raw)
        if node.get('kind') == 'constant':
            value = node.get('value')
            if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{64}', value) or int(value, 16) >= P:
                raise ValueError('noncanonical terminal source constant')
            node['value'] = int(value, 16)
        if identity not in observations:
            raise ValueError('unobserved terminal source')
        source[identity] = node
    pairs = None
    for swap_product in (False, True):
        for swap_add in ((False, True) if complement else (False,)):
            for swap_negative in ((False, True) if complement else (False,)):
                try:
                    candidate = match_source(expected(complement, swap_product, swap_add, swap_negative),
                                             source, inputs, item['product'])
                except ValueError:
                    continue
                if set(source) == {identity for _, identity in candidate}:
                    pairs = candidate
                    break
    if pairs is None:
        raise ValueError('original terminal source formula mismatch')

    def linear(identity):
        if identity not in observations or observations[identity][0] != 'linear':
            raise ValueError('unsupported terminal observation')
        return observations[identity][1]

    output = linear(item['product'])
    if len(output) != 1 or output[0][0] == 0 or output[0][1] != 1:
        raise ValueError('unsupported original terminal product output projection')
    if linear(item['asserted_equal']) != (((0, target),) if target else ()):
        raise ValueError('terminal assertion target observation mismatch')
    left, right = linear(inputs[0]), linear(inputs[1])
    factor = canonical(((0, 1),) + scaled(right, -1)) if complement else right
    multiplication = source[item['product']]
    expected_operands = (left, factor)
    actual_operands = (linear(multiplication['left']), linear(multiplication['right']))
    if actual_operands not in (expected_operands, expected_operands[::-1]):
        raise ValueError('original terminal product operand observation mismatch')
    return {'output': output, 'target': (((0, target),) if target else ()),
            'source': item, 'pairs': pairs}
