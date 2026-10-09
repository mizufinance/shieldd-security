"""Bounded search for the existing complete71-row leaf-key cofactor template.

Witness/auxiliary shifts are search candidates, never source or semantic facts.
Two full streaming replays must cover every mapped row and yield a unique map.
The existing cofactor extractor and generated kernel still independently check
the selected map; legal construction and native/caller roles remain separate.
"""
from . import transfer_relation as relation
from .transfer_balance_rows import canonical
from .transfer_encryption_dh_keys import infer_regulated_selectors


def find(checked, template, open_stream):
    inferred = infer_regulated_selectors(checked)
    metadata, identity = checked['metadata'], template.get('identity', {})
    if any(identity.get(a) != metadata[b] for a, b in
           [('relation_digest', 'relation_digest'), ('domain_size', 'domain_size'), ('stored_rows', 'full_rows')]):
        raise relation.RelationError('DH cofactor search exact template/occurrence identity required')
    selected = template.get('selected_rows')
    if not isinstance(selected, list) or len(selected) != 71:
        raise relation.RelationError('DH cofactor search complete71-row template required')
    domain, count, copy = metadata['domain_size'], metadata['full_rows'], metadata['constant_copy']
    source, previous = [], -1
    for row in selected:
        if not isinstance(row, dict) or set(row) != {'row', 'a', 'b'}:
            raise relation.RelationError('DH cofactor search original row shape')
        index = relation.natural(row['row'], count)
        if index <= previous:
            raise relation.RelationError('DH cofactor search sorted unique physical rows')
        previous = index
        for side in ('a', 'b'):
            relation.terms(row[side], domain)
        source.append(tuple(tuple((c, int(v, 16)) for c, v in row[side]) for side in ('a', 'b')))
    columns = {c for row in source for lc in row for c, _ in lc}
    witnesses, auxiliary = set(range(1980, 1987)), set(range(49716, 49780))
    if columns != {0, copy} | witnesses | auxiliary:
        raise relation.RelationError('DH cofactor search exact owned seven-witness/64-auxiliary support required')
    if (canonical([(0, 1), (copy, -1)]), ()) not in source:
        raise relation.RelationError('DH cofactor search real constant-copy link required')
    anchor = (((1982, 1),), ((49716, 1),))
    if anchor not in source:
        raise relation.RelationError('DH cofactor search exact owned preimage-square anchor required')
    starts, candidates = {}, {}
    for key in ('detection_key', 'payload_key'):
        leaves = inferred['selectors'][key]['leaf']
        point = [checked['derived'][leaf[1]] for leaf in leaves]
        if (any(leaf[0] != 'source' or leaf[1][0] != 1 for leaf in leaves) or
                any(lc != ((leaf[1][1] + 3, 1),) for lc, leaf in zip(point, leaves)) or
                point[1] != ((point[0][0][0] + 1, 1),)):
            raise relation.RelationError('DH cofactor search actual consecutive leaf-coordinate LCs required')
        starts[key] = point[0][0][0]
        candidates[key] = set()

    def full_replay(observer):
        with open_stream() as stream:
            actual = relation.inspect(stream, metadata['relation_digest'], observer)
        if actual['domain_size'] != domain or actual['stored_rows'] != count:
            raise relation.RelationError('DH cofactor search ordinary shape mismatch')
        return actual

    def propose(row):
        a, b = tuple(tuple((c, int(v, 16)) for c, v in row[side]) for side in ('a', 'b'))
        for key, first in starts.items():
            if a == ((first + 2, 1),) and len(b) == 1 and b[0][1] == 1:
                shift = b[0][0] - 49716
                if all(0 < c + shift < domain and c + shift != copy for c in auxiliary):
                    candidates[key].add(shift)
                    if len(candidates[key]) > 16:
                        raise relation.RelationError('DH cofactor search bounded16 anchor candidates exceeded')
    actual = full_replay(propose)
    maps, needed = {}, {}
    for key, shifts in candidates.items():
        if not shifts:
            raise relation.RelationError('DH cofactor search no captured preimage-square candidate')
        for shift in shifts:
            mapping = {c: c if c in (0, copy) else c + starts[key] - 1980 if c in witnesses else c + shift
                       for c in columns}
            if any(not 0 <= c < domain for c in mapping.values()):
                raise relation.RelationError('DH cofactor search candidate outside actual domain')
            maps[key, shift] = mapping
            values = {tuple(canonical((mapping[c], v) for c, v in lc) for lc in row) for row in source}
            needed[key, shift] = values
    expected = set().union(*needed.values())
    observed = set()

    def collect(row):
        value = tuple(tuple((c, int(v, 16)) for c, v in row[side]) for side in ('a', 'b'))
        if value in expected:
            observed.add(value)
    replay = full_replay(collect)
    if replay != actual:
        raise relation.RelationError('DH cofactor search ordinary replay identity changed')
    result = {}
    for key in candidates:
        complete = [mapping for (label, shift), mapping in maps.items()
                    if label == key and needed[label, shift] <= observed]
        if len(complete) != 1:
            raise relation.RelationError('DH cofactor search requires one complete71-row map per leaf')
        result[key] = complete[0]
    return dict(columns=result, identity=actual, anchor_candidates={key: len(value) for key, value in candidates.items()},
                scope='Unique complete71-row candidate coverage on two full ordinary replays only; '
                      'independent cofactor extraction/kernel, allocation/source/native/caller roles OPEN')
