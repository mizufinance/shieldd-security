"""Original arithmetic-row certificates for the eleven cofactor source cones.

This extends the strict group boundary selector. Every visited source node is
retained, including repeated mathematical expressions with different original
identities. No honest witness evaluator or replacement relation is consulted.
Selection remains extraction data until the generated Lean checks pass.
"""
from group_rows import select_boundary_rows
from hash_rows import canonical, scaled


def select(export, parameter_root):
    boundary = select_boundary_rows(export, parameter_root)
    outline = boundary['outline']
    # The boundary selector has already run the strict scalar ingress over all
    # exported raw rows and observations, including coefficient/dimension checks.
    def parse(terms):
        return tuple((column, int(encoded, 16)) for column, encoded in terms)

    raw = {row['index']: (parse(row['a']), parse(row['b'])) for row in export['rows']}
    observations = {item['source']: (item['kind'], parse(item['terms']))
                    for item in export['expressions']}
    table, squared = {}, {}
    for index, (a, b) in sorted(raw.items()):
        pair = tuple(canonical((0 if c == outline else c, v) for c, v in terms)
                     for terms in (a, b))
        table.setdefault(pair, index)
        squared.setdefault(pair[0], []).append((pair[1], index))

    cones, used = [], set(boundary['rows'])
    for matched in boundary['source']['cones']:
        identities = {identity for _, identity in matched['pairs']}
        inputs = {identity: slot for slot, identity in enumerate(matched['inputs'])}
        ordered, visiting, visited = [], set(), set()

        def visit(identity):
            if identity in visited:
                return
            if identity in visiting:
                raise ValueError('cyclic original group source')
            visiting.add(identity)
            node = matched['source'][identity]
            if identity not in inputs and node['kind'] in ('add', 'mul'):
                for side in ('left', 'right'):
                    child = node[side]
                    if child not in identities:
                        raise ValueError('uncertified original group dependency')
                    visit(child)
            visiting.remove(identity)
            visited.add(identity)
            ordered.append(identity)

        visit(matched['output'])
        if visited != identities:
            raise ValueError('unvisited matched group source')
        certificates = {}
        for identity in ordered:
            node = matched['source'][identity]
            kind, output = observations[identity]
            if kind != 'linear':
                raise ValueError('unsupported deferred group arithmetic')
            if identity in inputs:
                certificate = {'kind': 'input', 'slot': inputs[identity]}
            elif node['kind'] == 'constant':
                if output != canonical(((0, node['value']),)):
                    raise ValueError('wrong group constant observation')
                certificate = {'kind': 'constant', 'coefficient': node['value']}
            else:
                left, right = (observations[node[side]] for side in ('left', 'right'))
                if left[0] != 'linear' or right[0] != 'linear':
                    raise ValueError('unsupported deferred group consumer')
                left, right = left[1], right[1]
                if node['kind'] == 'add':
                    if output != canonical(left + right):
                        raise ValueError('wrong fused group add')
                    certificate = {'kind': 'add'}
                else:
                    constants = [(side, terms[0][1] if terms else 0)
                                 for side, terms in (('left', left), ('right', right))
                                 if not terms or len(terms) == 1 and terms[0][0] == 0]
                    if constants:
                        side, coefficient = constants[0]
                        other = right if side == 'left' else left
                        if output != scaled(other, coefficient):
                            raise ValueError('wrong folded group multiply')
                        certificate = {'kind': 'folded_' + side, 'coefficient': coefficient}
                    elif left == right:
                        if (left, output) not in table:
                            raise ValueError('missing original group square row')
                        certificate = {'kind': 'square', 'rows': [table[(left, output)]]}
                    else:
                        minus = canonical(left + scaled(right, -1))
                        plus = canonical(left + right)
                        candidates = [(first, table[(plus, canonical(aux + scaled(output, 4)))], aux)
                                      for aux, first in squared.get(minus, [])
                                      if (plus, canonical(aux + scaled(output, 4))) in table]
                        if not candidates:
                            raise ValueError('missing original group product rows')
                        first, second, auxiliary = min(candidates)
                        certificate = {'kind': 'product', 'rows': [first, second],
                                       'auxiliary': auxiliary}
            certificates[identity] = certificate
            used.update(certificate.get('rows', []))
        cones.append({**matched, 'ordered': ordered, 'certificates': certificates})
    return {**boundary, 'cones': cones, 'observations': observations,
            'rows': {index: raw[index] for index in sorted(used)},
            'scope': 'full original cofactor cone and boundary row selection; kernel checks pending'}
