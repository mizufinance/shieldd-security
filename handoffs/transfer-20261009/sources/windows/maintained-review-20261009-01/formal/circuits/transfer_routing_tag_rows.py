"""Capture the four tag decompositions and nested selects from physical rows.

All operands are validated source observations. These certificates describe
rows, not native hashing, native bit encoding, or complete Transfer semantics.
"""
import hashlib
from . import transfer_routing_rows as routing, transfer_relation as relation
from .transfer_fixed_spend import canonical, combine

SCHEMA = 'shieldd-transfer-routing-tag-rows-v1'


def extract(manifest, page, permutation, hash_pages, stream, accepted, params, base):
    selected = routing.boundaries(manifest, page, permutation, accepted, params)
    checked = selected['checked']
    others = [routing.pages.inspect_page(manifest, data, ordinal, accepted, params)
              for ordinal, data in zip([2, 3, 5, 6], hash_pages)]
    assert len(hash_pages) == len(others) == 4
    observed = dict(checked['observed'])
    for other in others:
        assert other['metadata']['records'] == checked['metadata']['records']
        assert other['metadata']['calls'] == checked['metadata']['calls']
        for handle, lc in other['observed'].items():
            assert handle not in observed or observed[handle] == lc
            observed[handle] = lc

    def value(ref):
        kind, handle = routing.pages.reference(ref)
        return canonical([(0, handle)]) if kind == 'native' else observed[handle]

    records = checked['records']
    flags = [value(ref) for ref in records['routing', 'flags', 0]]
    active = [value(ref) for ref in records['routing', 'active-prefix', 0]]
    bits = {tag: [[value(ref) for ref in records['routing', tag, slot]] for slot in range(2)]
            for tag in ['route-bits', 'random-bits', 'public-bits']}
    columns = {tag: [[routing._unit(lc, tag) for lc in group] for group in groups]
               for tag, groups in bits.items()}
    copy = checked['metadata']['constant_copy']
    outputs = [value(other['metadata']['hash']['output']) for other in others]
    touched = {c for lc in [*flags, *active, *outputs,
                            *(lc for groups in bits.values() for group in groups for lc in group)]
               for c, _ in lc}
    raw = {}; normalized = {}; terms = 0

    def observe(row):
        nonlocal terms
        a, b = (tuple((c, int(v, 16)) for c, v in row[key]) for key in ['a', 'b'])
        if not (any(c in touched for c, _ in a) or (len(a) <= 6 and len(b) <= 6)):
            return
        terms += len(a) + len(b)
        if len(raw) >= routing.MAX_ROWS or terms > routing.MAX_TERMS:
            raise relation.RelationError('bounded routing tag row pool exceeded')
        raw[row['row']] = a, b
        normalized[row['row']] = tuple(canonical((0 if c == copy else c, v) for c, v in lc) for lc in [a, b])

    identity = relation.inspect(stream, expected_relation=checked['metadata']['relation_digest'], row_observer=observe)
    assert identity == base['identity'] and base['metadata_sha256'] == selected['metadata_sha256']
    table = routing._Rows(raw, normalized, copy)
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    assert len(links) == 1
    used = {links[0]}
    swap = flags[0]
    words = []; decompositions = []; tag_steps = []
    for slot in range(2):
        left, right = outputs[1-slot], outputs[slot]
        weighted_route = canonical((c, pow(2, i, relation.MODULUS))
                                   for i, c in enumerate(columns['route-bits'][slot]))
        candidates = []
        for certificate in table.products(swap, combine(left, right, -1)):
            output = combine(right, certificate['output'])
            equation = combine(weighted_route, output, -1)
            positive = table.by_row.get((equation, ()), [])
            negative = table.by_row.get((canonical((c, -v) for c, v in equation), ()), [])
            if len(positive) + len(negative) == 1:
                candidates.append((certificate, output))
        if len(candidates) != 1:
            raise relation.RelationError('unique reconstructed route word product required: ' + str(slot)
                                         + ' candidates=' + str(len(candidates)))
        word_select, word = candidates[0]
        assert word == flags[3+slot], 'captured route-word expression must match its physical swap product'
        used.update(word_select['rows'])
        words.append(dict(output=word, swapped=swap, left=left, right=right, certificate=word_select))
        for tag, output in [('route-bits', word), ('random-bits', outputs[2+slot])]:
            plan, part = routing._permutation(dict(swapped=bits[tag][slot][0], output=output), table)
            assert plan['columns'] == columns[tag][slot]
            used.update(part)
            decompositions.append(dict(tag=tag, slot=slot, plan=plan))
        weighted = canonical((c, pow(2, i, relation.MODULUS)) for i, c in enumerate(columns['public-bits'][slot]))
        reconstruct = table.exact(combine(weighted, flags[5+slot], -1), (), 'public tag reconstruction ' + str(slot), True)
        used.add(reconstruct)
        for index in range(32):
            route = bits['route-bits'][slot][index]
            random = bits['random-bits'][slot][index]
            public = bits['public-bits'][slot][index]
            inner = table.product(active[index], combine(route, random, -1), 'tag prefix ' + str((slot, index)))
            prefix = combine(random, inner['output'])
            target = combine(public, random, -1)
            difference = combine(prefix, random, -1)
            candidates = table.products(flags[1+slot], difference, target)
            candidates += [pair for pair in table.pairs(flags[1+slot], difference)
                           if pair['output'] == target]
            if len(candidates) != 1:
                raise relation.RelationError('unique physical tag assertion required: '
                                             + str((slot, index)) + ' candidates=' + str(len(candidates)))
            outer = candidates[0]
            boolean = table.exact(public, public, 'public tag Boolean ' + str((slot, index)))
            used.update(inner['rows']); used.update(outer['rows']); used.add(boolean)
            tag_steps.append(dict(slot=slot, index=index, active=active[index], meaningful=flags[1+slot],
                                  route=route, random=random, public=public, prefix=prefix,
                                  inner=inner, outer=outer, public_boolean_row=boolean))
    rows = [dict(row=i, a=[[c, f'{v:064x}'] for c, v in raw[i][0]],
                          b=[[c, f'{v:064x}'] for c, v in raw[i][1]]) for i in sorted(used)]
    return dict(schema=SCHEMA, identity=identity, metadata_sha256=selected['metadata_sha256'],
                source_sha256=hashlib.sha256(page).hexdigest(), selected_rows=rows,
                plan=dict(constant_link=links[0], words=words, decompositions=decompositions,
                          tag_steps=tag_steps, flags=flags),
                candidate_rows=len(raw), candidate_terms=terms, source_only=True, kernel_run=False,
                scope='Four physical canonical255 chains and64 nested tag select assertions; native hash/codec/caller/full Transfer open')
