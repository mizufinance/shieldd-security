"""Choose local Compiler.NodeCertificate data for actual authorization cones.

Selection is not a proof. The Lean generator must instantiate each selected
constructor against the raw emitted rows and the exact source graph. In
particular, column-copy rewriting is justified by Compiler.unoutline_rows_sound,
never by claiming the private copy equals one without its emitted linking row.
"""
import re
try:
    from .poseidon_graph import P, match_export, parameters
except ImportError:
    from poseidon_graph import P, match_export, parameters


def canonical(terms):
    result = {}
    for column, value in terms:
        result[column] = (result.get(column, 0) + value) % P
    return tuple((column, value) for column, value in sorted(result.items()) if value)


def scaled(terms, coefficient):
    return canonical((column, value * coefficient) for column, value in terms)


def select(export, parameter_root):
    calls = match_export(export, parameter_root)
    domain, count = export['domain_size'], export['row_count']
    if (type(domain) is not int or domain < 4 or domain & (domain - 1)
            or type(count) is not int or not 0 < count <= domain
            or export['public_inputs'] != 1 or export['committed_blocks'] != [1]
            or not re.fullmatch('[0-9a-f]{64}', export['relation_digest'])):
        raise ValueError('invalid actual Transfer relation identity/layout')

    def parse(terms):
        parsed, previous = [], -1
        for column, encoded in terms:
            if type(column) is not int or not previous < column < domain:
                raise ValueError('invalid/noncanonical LC columns')
            if not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded):
                raise ValueError('noncanonical LC coefficient')
            coefficient = int(encoded, 16)
            if not 0 < coefficient < P:
                raise ValueError('zero/out-of-field LC coefficient')
            parsed.append((column, coefficient))
            previous = column
        return tuple(parsed)

    raw_rows = {}
    for row in export['rows']:
        index = row['index']
        if type(index) is not int or not 0 <= index < count:
            raise ValueError('invalid source row index')
        pair = (parse(row['a']), parse(row['b']))
        if index in raw_rows and raw_rows[index] != pair:
            raise ValueError('contradictory source row index')
        raw_rows[index] = pair
    links = [(index, a[1][0]) for index, (a, b) in raw_rows.items()
             if not b and len(a) == 2 and a[0] == (0, 1)
             and a[1][1] == P - 1 and a[1][0] >= 3]
    if len(links) != 1:
        raise ValueError('missing/ambiguous outlined-one linking row')
    link_index, outline = links[0]

    def unoutline(terms):
        return canonical((0 if column == outline else column, value) for column, value in terms)

    table, squared = {}, {}
    for index, (a, b) in sorted(raw_rows.items()):
        pair = (unoutline(a), unoutline(b))
        table.setdefault(pair, index)
        squared.setdefault(pair[0], []).append((pair[1], index))
    observations = {item['source']: (item['kind'], parse(item['terms']))
                    for item in export['expressions']}
    if any(column == outline for _, terms in observations.values() for column, _ in terms):
        raise ValueError('unexpected outlined copy in pre-outline source observation')
    used = {link_index}
    authorization_links = []
    # The closed IVK-only scope does not claim action-key/statement linkage.
    for axis in (() if export.get('hash_scope') == 'transfer-ivk-only' else ('x', 'y')):
        ownership = export['ownership']
        left_kind, left = observations[ownership[f'action.computed_rk.{axis}']]
        right_kind, right = observations[ownership[f'statement.rk.{axis}']]
        if left_kind != 'linear' or right_kind != 'linear':
            raise ValueError('unsupported action key assertion expression')
        pair = (canonical(left + scaled(right, -1)), ())
        reverse = (canonical(right + scaled(left, -1)), ())
        if pair in table:
            index, reversed_row = table[pair], False
        elif reverse in table:
            index, reversed_row = table[reverse], True
        else:
            raise ValueError('missing actual computed/statement action key equality row')
        used.add(index)
        authorization_links.append({'axis': axis, 'computed': left, 'statement': right,
                                    'row': index, 'reversed': reversed_row,
                                    'computed_source': ownership[f'action.computed_rk.{axis}'],
                                    'statement_source': ownership[f'statement.rk.{axis}']})
    result = []
    for call in calls:
        identities = {actual for _, actual in call['pairs']}
        boundaries = {identity: slot for slot, identity in enumerate(call['inputs'])}
        certificates = {}
        for identity in sorted(identities, key=lambda x: (x[0] == 'n', x[0], int(x[1:]))):
            node = call['source'][identity]
            kind, output = observations[identity]
            if identity in boundaries:
                if kind != 'linear':
                    raise ValueError('unsupported non-linear input boundary')
                if (export.get('hash_scope') != 'transfer-ivk-only'
                        and identity.startswith('w') and output != ((int(identity[1:]) + 3, 1),)):
                    raise ValueError('wrong original witness input projection')
                certificates[identity] = {'kind': 'input', 'slot': boundaries[identity]}
                continue
            if node['kind'] == 'constant':
                if kind != 'linear' or output != canonical([(0, node['value'])]):
                    raise ValueError('constant observation mismatch')
                certificates[identity] = {'kind': 'constant', 'value': node['value']}
                continue
            left_kind, left = observations[node['left']]
            right_kind, right = observations[node['right']]
            if left_kind != 'linear' or right_kind != 'linear':
                raise ValueError('unsupported deferred-square consumer')
            if node['kind'] == 'add':
                if kind != 'linear' or output != canonical(left + right):
                    raise ValueError('fused add observation mismatch')
                certificate = {'kind': 'add'}
            elif kind == 'square':
                if output != left or output != right:
                    raise ValueError('deferred square observation mismatch')
                certificate = {'kind': 'deferred'}
            else:
                constants = [(side, terms[0][1] if terms else 0)
                             for side, terms in [('left', left), ('right', right)]
                             if not terms or (len(terms) == 1 and terms[0][0] == 0)]
                if constants:
                    side, coefficient = constants[0]
                    if output != scaled(right if side == 'left' else left, coefficient):
                        raise ValueError('folded multiplication observation mismatch')
                    certificate = {'kind': 'folded_' + side, 'coefficient': coefficient}
                elif left == right:
                    pair = (left, output)
                    if pair not in table:
                        raise ValueError('missing actual square row')
                    certificate = {'kind': 'square', 'rows': [table[pair]]}
                else:
                    minus, plus = canonical(left + scaled(right, -1)), canonical(left + right)
                    candidates = []
                    for auxiliary, minus_index in squared.get(minus, []):
                        pair = (plus, canonical(auxiliary + scaled(output, 4)))
                        if pair in table:
                            candidates.append((minus_index, table[pair], auxiliary))
                    if not candidates:
                        raise ValueError('missing actual multiplication rows')
                    minus_index, plus_index, auxiliary = min(candidates)
                    certificate = {'kind': 'product', 'rows': [minus_index, plus_index],
                                   'auxiliary': auxiliary}
            used.update(certificate.get('rows', []))
            certificates[identity] = certificate
        # The semantic proof is generated per permutation round. Unused final
        # MDS coordinates may be represented by derived LCs, but never presented
        # as observed source outputs; the actual requested output is checked.
        graph = call['graph']
        params = parameters(parameter_root / ('poseidon381.json' if graph['width'] == 3
                                              else 'poseidon381-wide.json'), graph['width'])
        matches = {}
        for expected_id, actual_id in call['pairs']:
            matches.setdefault(expected_id, set()).add(actual_id)
        terms_cache = {}

        def graph_terms(index):
            if index in terms_cache:
                return terms_cache[index]
            node = graph['nodes'][index]
            if index in matches:
                values = {observations[identity] for identity in matches[index]}
                if len(values) != 1 or next(iter(values))[0] != 'linear':
                    raise ValueError('unsupported unequal/non-linear shared boundary expressions')
                value = next(iter(values))[1]
            elif node['kind'] == 'constant':
                value = canonical([(0, node['value'])])
            elif node['kind'] == 'add':
                value = canonical(graph_terms(node['left']) + graph_terms(node['right']))
            elif node['kind'] == 'mul':
                left, right = graph['nodes'][node['left']], graph['nodes'][node['right']]
                if left['kind'] == 'constant':
                    value = scaled(graph_terms(node['right']), left['value'])
                elif right['kind'] == 'constant':
                    value = scaled(graph_terms(node['left']), right['value'])
                else:
                    raise ValueError('nonlinear node has no actual source observation')
            else:
                raise ValueError('unobserved hash input')
            terms_cache[index] = value
            return value

        previous = [canonical([(0, graph['arity'] * 256 + graph['domain'])])] + [()] * (graph['width'] - 1)
        segments = []
        for segment in graph['segments']:
            before = [graph_terms(i) for i in segment['before']]
            after = [graph_terms(i) for i in segment['after']]
            if before != previous:
                raise ValueError('broken actual hash segment boundary')
            if segment['kind'] == 'absorb':
                expected_after = list(before)
                for i, identity in enumerate(segment['inputs']):
                    expected_after[i + 1] = canonical(before[i + 1] + graph_terms(identity))
                if after != expected_after:
                    raise ValueError('incorrect actual absorption/padding')
                segments.append({'kind': 'absorb', 'before': before, 'after': after,
                                 'input_ids': segment['inputs']})
            else:
                index = segment['round']
                shifted = [graph_terms(i) for i in segment['shifted']]
                transformed = [graph_terms(i) for i in segment['transformed']]
                fifths, round_rows = {}, set()
                for i in range(graph['width']):
                    if shifted[i] != canonical(before[i] + ((0, params['ark'][index][i]),)):
                        raise ValueError('incorrect actual round constant addition')
                    if i not in segment['powers']:
                        if transformed[i] != shifted[i]:
                            raise ValueError('incorrect partial-round linear column')
                        continue
                    base = shifted[i]
                    if not base or (len(base) == 1 and base[0][0] == 0):
                        coefficient = base[0][1] if base else 0
                        if transformed[i] != canonical([(0, pow(coefficient, 5, P))]):
                            raise ValueError('incorrect constant fifth power')
                        fifths[i] = {'kind': 'constant', 'coefficient': coefficient}
                    else:
                        power = segment['powers'][i]
                        square, fourth = graph_terms(power['square']), graph_terms(power['fourth'])
                        first, second = (base, square), (square, fourth)
                        if first not in table or second not in table:
                            raise ValueError('missing exact fifth square rows')
                        minus, plus = canonical(fourth + scaled(base, -1)), canonical(fourth + base)
                        candidates = [(minus_index, table[(plus, canonical(aux + scaled(transformed[i], 4)))], aux)
                                      for aux, minus_index in squared.get(minus, [])
                                      if (plus, canonical(aux + scaled(transformed[i], 4))) in table]
                        if not candidates:
                            raise ValueError('missing exact fifth product rows')
                        minus_index, plus_index, auxiliary = min(candidates)
                        indices = [table[first], table[second], minus_index, plus_index]
                        round_rows.update(indices)
                        fifths[i] = {'kind': 'arithmetic', 'square': square, 'fourth': fourth,
                                     'auxiliary': auxiliary, 'rows': indices}
                for i, coefficients in enumerate(params['mds']):
                    mixed = canonical(term for coefficient, state in zip(coefficients, transformed)
                                      for term in scaled(state, coefficient))
                    if after[i] != mixed:
                        raise ValueError('incorrect actual MDS mixing')
                used.update(round_rows)
                segments.append({'kind': 'round', 'chunk': segment['chunk'], 'index': index,
                                 'before_ids': segment['before'], 'after_ids': segment['after'],
                                 'before': before, 'shifted': shifted, 'transformed': transformed,
                                 'after': after, 'fifths': fifths, 'rows': sorted(round_rows)})
            previous = after
        if observations[call['output']] != ('linear', previous[1]):
            raise ValueError('wrong actual hash output coordinate')
        result.append({'role': call['role'], 'call': call, 'certificates': certificates,
                       'segments': segments, 'parameters': params})
    return {'outline': outline, 'constant_link': link_index, 'calls': result,
            'rows': {index: raw_rows[index] for index in sorted(used)},
            'authorization_links': authorization_links,
            'observations': observations,
            'scope': 'local certificate selection only; kernel instantiation required'}
