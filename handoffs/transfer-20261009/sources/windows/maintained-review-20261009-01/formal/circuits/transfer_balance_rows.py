"""Bounded selected-source/actual-row checks for the current signed balance.

This is an extraction check, not a Lean proof or registry qualification. Source
handle capture and upstream lowering remain explicit joins. Every accepted row
is checked against the complete digest-validated ordinary relation stream.
"""
import hashlib
import re
from . import transfer_relation as relation

P = relation.MODULUS


def canonical(terms):
    result = {}
    for column, coefficient in terms:
        result[column] = (result.get(column, 0) + coefficient) % P
    return tuple(sorted((column, coefficient) for column, coefficient in result.items() if coefficient))


def combine(left, right, factor=1):
    return canonical(list(left) + [(column, factor * coefficient) for column, coefficient in right])


def source_index(value):
    if not isinstance(value, list) or len(value) != 2:
        raise relation.RelationError('malformed balance source handle')
    return (relation.natural(value[0], 3), relation.natural(value[1], 2**32))


def scoped_omission_controls(metadata_bytes, checked):
    """Concrete modular-field assignments for the selected relation only.

    The full Transfer constraints are not evaluated. Successful controls require
    every retained selected row to hold and exactly the omitted row to reject.
    """
    metadata = relation.record(metadata_bytes)
    roles = {role: item['row'] for item in checked['templates'] for role in item['roles']}
    rows = {row['row']: row for row in checked['selected_rows']}
    if len(checked['products']) != 1:
        raise relation.RelationError('omission controls require one selected product')
    minus = rows[checked['products'][0]['rows'][0]]
    if len(minus['b']) != 1 or int(minus['b'][0][1],16) != 1:
        raise relation.RelationError('omission controls require a unit auxiliary')
    auxiliary = minus['b'][0][0]
    def evaluate(terms, rho):
        return sum(int(encoded,16)*rho.get(column,0) for column,encoded in terms) % P
    zero = {0:1, metadata['constant_copy']:1}
    if any(evaluate(row['a'],zero)**2 % P != evaluate(row['b'],zero) for row in rows.values()):
        raise relation.RelationError('selected all-zero balance positive baseline failed')
    cases = []
    for name in ['input0-top-boolean', 'input0-reconstruction', 'negative-boolean', 'signed-equation', 'product-minus', 'product-plus']:
        rho = {0:1, metadata['constant_copy']:1}
        if name in ['input0-top-boolean','input0-reconstruction']:
            omitted = roles['range0.boolean127'] if name == 'input0-top-boolean' else roles['range0.reconstruction']
            rho[metadata['handles'][0]['values'][0][1]+3] = 2**128
            if name == 'input0-top-boolean':
                rho[metadata['handles'][0]['bits'][127][1]+3] = 2
            rho[metadata['handles'][4]['values'][2][1]+3] = 2**128
            rho[metadata['handles'][4]['bits'][128][1]+3] = 1
        elif name == 'negative-boolean':
            omitted = roles['negative.boolean']
            rho[metadata['handles'][4]['values'][1][1]+3] = 2
        else:
            omitted = roles['signed.equation'] if name == 'signed-equation' else checked['products'][0]['rows'][0 if name == 'product-minus' else 1]
            rho[metadata['handles'][0]['values'][0][1]+3] = 1
            rho[metadata['handles'][0]['bits'][0][1]+3] = 1
            if name.startswith('product-'):
                product_node = checked['products'][0]['node']
                expression = next(item for item in metadata['expressions'] if item['source'] == [2,product_node])
                product_column = expression['terms'][0][0]
                selection = next(item for item in metadata['expressions'] if item['source'] == metadata['handles'][4]['values'][3])
                coefficient = next(int(value,16) for column,value in selection['terms'] if column == product_column)
                rho[product_column] = pow(coefficient,-1,P)
        rho[auxiliary] = ((-4*rho[product_column]) % P if name == 'product-minus' else 0 if name == 'product-plus' else evaluate(minus['a'],rho)**2 % P)
        rejected = {index for index,row in rows.items()
                    if evaluate(row['a'],rho)**2 % P != evaluate(row['b'],rho)}
        if rejected != {omitted}:
            raise relation.RelationError('intended selected-row omission counterexample not observed')
        amounts = [rho.get(metadata['handles'][i]['values'][0][1]+3,0) for i in range(4)]
        sign = rho.get(metadata['handles'][4]['values'][1][1]+3,0)
        magnitude = rho.get(metadata['handles'][4]['values'][2][1]+3,0)
        violated = (amounts[0] >= 2**128 if name.startswith('input0-') else
                    sign not in (0,1) if name == 'negative-boolean' else
                    sign in (0,1) and amounts[0]+amounts[1]-amounts[2]-amounts[3] !=
                    (-magnitude if sign else magnitude))
        if not violated:
            raise relation.RelationError('claimed selected-slice semantic violation not observed')
        cases.append({'name':name, 'omitted_original_row':omitted,
                      'original_rejected_rows':sorted(rejected), 'remaining_selected_rows_satisfied':True,
                      'assignment':sorted(rho.items()),
                      'violates':'input0 < 2^128' if name.startswith('input0-') else 'negative is Boolean' if name=='negative-boolean' else 'exact integer net balance'})
    return {'scope':'explicit selected-row modular-field counterexamples only; full Transfer constraints not evaluated',
            'all_zero_selected_balance_satisfied':True, 'cases':cases}


def inspect(metadata_bytes, stream, expected_relation):
    if not isinstance(expected_relation, str) or not re.fullmatch('[0-9a-f]{64}', expected_relation):
        raise relation.RelationError('exact expected relation digest required')
    if len(metadata_bytes) > 2**20:
        raise relation.RelationError('balance metadata exceeds bound')
    metadata = relation.record(metadata_bytes)
    required = {'schema', 'relation_digest', 'domain_size', 'stored_rows', 'ordinary_full_ordered_rows_equal',
                'scope', 'constant_copy', 'handles', 'expressions', 'nodes'}
    if (set(metadata) != required or metadata['schema'] != 'shieldd-transfer-balance-inspection-v1'
            or metadata['relation_digest'] != expected_relation
            or metadata['ordinary_full_ordered_rows_equal'] is not True
            or metadata['scope'] != 'source handles and pre-outline linear combinations only; semantic row certificates remain open'):
        raise relation.RelationError('unknown/unmatched balance metadata')
    domain = relation.natural(metadata['domain_size'])
    row_count = relation.natural(metadata['stored_rows'])
    copy = relation.natural(metadata['constant_copy'], domain)
    if copy <= 2:
        raise relation.RelationError('invalid private constant copy')
    handles = metadata['handles']
    if not isinstance(handles, list) or len(handles) != 5:
        raise relation.RelationError('balance handle shape changed')
    ranges, signed = [], None
    for i, item in enumerate(handles):
        if not isinstance(item, dict) or set(item) != {'role', 'values', 'bits'}:
            raise relation.RelationError('unknown balance handle fields')
        width, arity, role = (128, 1, 'amount') if i < 4 else (129, 4, 'signed')
        if (item['role'] != role or not isinstance(item['values'], list) or len(item['values']) != arity
                or not isinstance(item['bits'], list) or len(item['bits']) != width):
            raise relation.RelationError('balance amount/sign/range arity changed')
        values, bits = list(map(source_index, item['values'])), list(map(source_index, item['bits']))
        if len(set(bits)) != width or any(bit[0] != 1 for bit in bits):
            raise relation.RelationError('balance bits must be distinct source witnesses')
        ranges.append((values[0] if i < 4 else values[2], bits))
        if i == 4:
            signed = values
    expressions = {}
    if not isinstance(metadata['expressions'], list) or len(metadata['expressions']) > 1024:
        raise relation.RelationError('selected expression bound exceeded')
    previous = None
    for item in metadata['expressions']:
        if not isinstance(item, dict) or set(item) != {'source', 'terms'}:
            raise relation.RelationError('unknown expression fields')
        key = source_index(item['source'])
        if previous is not None and key <= previous:
            raise relation.RelationError('noncanonical selected expression order')
        previous = key
        relation.terms(item['terms'], domain)
        terms = tuple((column, int(encoded, 16)) for column, encoded in item['terms'])
        if key[0] == 1 and terms != ((3 + key[1], 1),):
            raise relation.RelationError('source witness must map to exact private column 3+index')
        if key[0] == 0 and any(column != 0 for column, _ in terms):
            raise relation.RelationError('source constant must be pre-outline constant')
        expressions[key] = terms
    def expression(key):
        if key not in expressions:
            raise relation.RelationError('missing selected source expression')
        return expressions[key]
    roots = [ranges[i][0] for i in range(4)] + signed[1:3]
    all_bits = [bit for _, bits in ranges for bit in bits]
    if (len(set(roots)) != 6 or any(root[0] != 1 for root in roots)
            or len(set(all_bits)) != len(all_bits) or set(all_bits) & set(roots)):
        raise relation.RelationError('amount/sign/magnitude roots overlap')
    witness_columns = [terms[0][0] for key, terms in expressions.items() if key[0] == 1]
    if len(set(witness_columns)) != len(witness_columns):
        raise relation.RelationError('distinct source witnesses share a private column')
    nodes = {}
    previous = -1
    if not isinstance(metadata['nodes'], list) or len(metadata['nodes']) > 128:
        raise relation.RelationError('source closure bound exceeded')
    for node in metadata['nodes']:
        if not isinstance(node, dict) or set(node) != {'index', 'multiply', 'left', 'right'} or type(node['multiply']) is not bool:
            raise relation.RelationError('unknown source node')
        index = relation.natural(node['index'], 2**32)
        if index <= previous:
            raise relation.RelationError('noncanonical source node order')
        previous = index
        left, right = source_index(node['left']), source_index(node['right'])
        if any(key[0] == 2 and key[1] >= index for key in [left, right]):
            raise relation.RelationError('non-topological source closure')
        nodes[(2, index)] = (node['multiply'], left, right)
    # Independent polynomial interpretation of the bounded source DAG.
    polynomials = {root: {(i,): 1} for i, root in enumerate(roots)}
    visited = set()
    def polynomial(key):
        visited.add(key)
        if key in polynomials:
            return polynomials[key]
        if key[0] == 0:
            value = expression(key)
            result = {(): value[0][1]} if value else {}
        elif key in nodes:
            multiply, left, right = nodes[key]
            a, b = polynomial(left), polynomial(right)
            result = {}
            if multiply:
                for x, v in a.items():
                    for y, w in b.items():
                        monomial = tuple(sorted(x + y))
                        if len(monomial) > 4 or len(result) > 64:
                            raise relation.RelationError('bounded source polynomial complexity exceeded')
                        result[monomial] = (result.get(monomial, 0) + v*w) % P
            else:
                result = dict(a)
                for x, v in b.items(): result[x] = (result.get(x, 0) + v) % P
            result = {x: v for x, v in result.items() if v}
        else:
            raise relation.RelationError('source closure has unnamed boundary')
        polynomials[key] = result
        return result
    if polynomial(signed[0]) != {(0,): 1, (1,): 1, (2,): P-1, (3,): P-1}:
        raise relation.RelationError('source difference is not ordered input-output net')
    if polynomial(signed[3]) != {(5,): 1, (4, 5): P-2}:
        raise relation.RelationError('source selection is not signed magnitude')
    if set(nodes) - visited:
        raise relation.RelationError('unreachable source nodes')
    if set(expressions) != visited | set(roots) | set(all_bits):
        raise relation.RelationError('missing or extra selected source expressions')
    def outlined(terms):
        return canonical((copy if column == 0 else column, coefficient) for column, coefficient in terms)
    required_rows = {}
    def require(name, a, b=(), outline=True):
        key = (outlined(a), outlined(b)) if outline else (canonical(a), canonical(b))
        required_rows.setdefault(key, []).append(name)
    require('constant-copy', [(0, 1), (copy, -1)], outline=False)
    for i, (value, bits) in enumerate(ranges):
        reconstruction = []
        for j, bit in enumerate(bits):
            terms = expression(bit)
            require(f'range{i}.boolean{j}', terms, terms)
            reconstruction.extend((column, coefficient * 2**j) for column, coefficient in terms)
        require(f'range{i}.reconstruction', combine(reconstruction, expression(value), -1))
    require('negative.boolean', expression(signed[1]), expression(signed[1]))
    require('signed.equation', combine(expression(signed[0]), expression(signed[3]), -1))
    products, candidate_as = [], set()
    for key, (multiply, left, right) in nodes.items():
        a, b, out = expression(left), expression(right), expression(key)
        if not multiply:
            if combine(a, b) != out: raise relation.RelationError('source addition LC mismatch')
        elif all(column == 0 for column, _ in a) or all(column == 0 for column, _ in b):
            constant, terms = (a, b) if all(column == 0 for column, _ in a) else (b, a)
            coefficient = constant[0][1] if constant else 0
            if canonical((column, coefficient*v) for column, v in terms) != out:
                raise relation.RelationError('source constant product LC mismatch')
        elif a == b:
            require(f'node{key[1]}.square', a, out)
        else:
            minus, plus = outlined(combine(a, b, -1)), outlined(combine(a, b))
            products.append((key[1], minus, plus, outlined(out)))
            candidate_as.update([minus, plus])
    matched, candidates, selected_rows = {}, {}, {}
    def observe(row):
        a = tuple((column, int(encoded, 16)) for column, encoded in row['a'])
        b = tuple((column, int(encoded, 16)) for column, encoded in row['b'])
        if (a, b) in required_rows:
            matched.setdefault((a, b), row['row'])
            selected_rows[row['row']] = row
        if a in candidate_as:
            candidates.setdefault(a, []).append((b, row['row']))
            selected_rows[row['row']] = row
            if len(candidates[a]) > 256:
                raise relation.RelationError('selected product row candidate bound exceeded')
    identity = relation.inspect(stream, expected_relation=expected_relation, row_observer=observe)
    if identity['domain_size'] != domain or identity['stored_rows'] != row_count:
        raise relation.RelationError('metadata/full relation shape mismatch')
    if set(required_rows) - set(matched):
        missing = next(iter(set(required_rows) - set(matched)))
        raise relation.RelationError('missing actual template: '+required_rows[missing][0])
    product_rows = []
    for node, minus, plus, out in products:
        pairs = [(i, j) for auxiliary, i in candidates.get(minus, [])
                 for linear, j in candidates.get(plus, []) if linear == combine(auxiliary, out, 4)]
        if not pairs: raise relation.RelationError(f'missing paired product rows for node{node}')
        product_rows.append({'node': node, 'rows': list(pairs[0])})
    return {'identity': identity, 'metadata_sha256': hashlib.sha256(metadata_bytes).hexdigest(),
            'templates': [{'roles': roles, 'row': matched[key]} for key, roles in required_rows.items()],
            'products': product_rows, 'source_nodes': len(nodes), 'selected_expressions': len(expressions),
            'selected_rows': [selected_rows[index] for index in sorted(set(matched.values()) |
                {index for product in product_rows for index in product['rows']})],
            'scope': 'bounded source polynomial and actual row-template extraction only; Lean/source/key/group joins remain open'}
