"""Bounded derivative ORDER-1 comparator certificates for recovery randomizers.

Accepted capsule metadata supplies only real randomizer/bit roles. Intermediate
LCs are inferred from unique physical row pairs, never invented source handles.
The full ordinary stream is checked once for both slots. Extraction/generation
does not qualify the runtime observer or certify native encryption.
"""
import hashlib
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from . import transfer_recovery_ranges as ranges
from .transfer_balance_rows import canonical, combine
from .transfer_canonical_balance import ORDER
from .generate_transfer_canonical_balance import generate_linear_checked

MAX_CANDIDATE_ROWS = 16384
MAX_CANDIDATE_TERMS = 131072
ONE = ((0, 1),)


def _boundaries(data, output_data, accepted_roles):
    selected = [ranges.boundary(data, output_data, accepted_roles, slot) for slot in (0, 1)]
    if set(selected[0]['columns']) & set(selected[1]['columns']):
        raise relation.RelationError('recovery canonical bit roles overlap')
    return selected


def _chain(selected, raw, normalized):
    """Reconstruct the exact pinned less_or_equal recurrence from actual rows."""
    by_a = {}
    by_row = {}
    for index, row in normalized.items():
        by_a.setdefault(row[0], []).append((row[1], index))
        by_row.setdefault(row, []).append(index)

    def direct(a, b, role, signed=False):
        matches = list(by_row.get((a, b), []))
        negative = canonical((c, -v) for c, v in a)
        if signed and negative != a: matches += by_row.get((negative, b), [])
        if len(matches) != 1:
            raise relation.RelationError('recovery canonical unique actual row: ' + role)
        return matches[0]

    copy = selected['checked']['metadata']['constant_copy']
    constant = (canonical([(0, 1), (copy, -1)]), ())
    constant_matches = [i for i, row in raw.items() if row == constant]
    if len(constant_matches) != 1:
        raise relation.RelationError('recovery canonical unique constant link')
    templates = [dict(roles=['constant-copy'], row=constant_matches[0])]
    steps, products, used = [], [], {constant_matches[0]}
    before = ONE
    for index, column in enumerate(selected['columns']):
        left = ((column, 1),); right = ((ORDER - 1) >> index) & 1
        both = combine(ONE, left, -1) if right else ()
        factor = combine(combine(ONE, left, -1), ((0, right),) if right else ())
        factor = combine(factor, both, -2)
        boolean = direct(left, left, 'boolean' + str(index))
        templates.append(dict(roles=['boolean' + str(index)], row=boolean)); used.add(boolean)
        if index == 0:
            product, indices = factor, []
        else:
            minus, plus = combine(before, factor, -1), combine(before, factor)
            matches = []
            # The maintained StepData product template has the exact source
            # operand orientation. Swapped rows are refused, not silently cast.
            for auxiliary, first in by_a.get(minus, []):
                for total, second in by_a.get(plus, []):
                    if first == second: continue
                    output = canonical((c, v * pow(4, -1, relation.MODULUS))
                                       for c, v in combine(total, auxiliary, -1))
                    matches.append((output, first, second))
            matches = list(dict.fromkeys(matches))
            if len(matches) != 1:
                raise relation.RelationError('recovery canonical unique product pair: ' + str(index))
            product, first, second = matches[0]; indices = [first, second]
            products.append(dict(step=index, rows=indices)); used.update(indices)
        after = combine(both, product)
        steps.append(dict(before=before, left=left, right=right, factor=factor,
                          product=product, after=after))
        before = after
    reconstruction = direct(combine(selected['weighted'], ((selected['value'], 1),), -1), (),
                            'reconstruction', True)
    endpoint = direct(combine(before, ONE, -1), (), 'endpoint', True)
    templates += [dict(roles=['reconstruction'], row=reconstruction), dict(roles=['endpoint'], row=endpoint)]
    used.update((reconstruction, endpoint))
    return dict(steps=steps, templates=templates, products=products), used


def extract(data, stream, output_data, accepted_roles):
    """One complete replay, bounded candidate collection, two exact chains."""
    boundaries = _boundaries(data, output_data, accepted_roles)
    metadata = boundaries[0]['checked']['metadata']; copy = metadata['constant_copy']
    bit_columns = {column for selected in boundaries for column in selected['columns']}
    raw, normalized, records = {}, {}, {}; terms = 0
    def observe(row):
        nonlocal terms
        a, b = (tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
        if not (any(c in bit_columns for c, _ in a) or not b and len(a) <= 3): return
        terms += len(a) + len(b)
        if len(records) >= MAX_CANDIDATE_ROWS or terms > MAX_CANDIDATE_TERMS:
            raise relation.RelationError('recovery canonical bounded candidate inventory exceeded')
        index = row['row']; raw[index] = (a, b); records[index] = row
        normalized[index] = tuple(canonical((0 if c == copy else c, v) for c, v in lc) for lc in (a, b))
    identity = relation.inspect(stream, expected_relation=metadata['relation_digest'], row_observer=observe)
    if identity['domain_size'] != metadata['domain_size'] or identity['stored_rows'] != metadata['full_rows']:
        raise relation.RelationError('recovery canonical ordinary identity/shape')
    slots, all_used = [], set()
    for selected in boundaries:
        chain, used = _chain(selected, raw, normalized)
        chain.update(slot=selected['slot'], selected_rows=[records[i] for i in sorted(used)],
                     identity=identity, metadata_sha256=hashlib.sha256(data).hexdigest())
        slots.append(chain); all_used.update(used)
    return dict(schema='shieldd-recovery-canonical-row-derivative-v1',
                metadata_sha256=hashlib.sha256(data).hexdigest(), identity=identity, slots=slots,
                candidate_rows=len(records), selected_rows=len(all_used),
                scope='two actual ORDER-1 comparator row certificates; native/nonzero/group joins open')


def _json_value(value):
    import json
    # Compare the canonical representation, so true/1 and false/0 cannot alias
    # through Python's equality while validating persisted typed derivatives.
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def generate(data, extracted, output_data, accepted_roles, slot):
    """Recheck persisted row certificates before rendering one finite candidate."""
    slot = relation.natural(slot, 2)
    boundaries = _boundaries(data, output_data, accepted_roles)
    metadata = boundaries[slot]['checked']['metadata']; digest = hashlib.sha256(data).hexdigest()
    if (not isinstance(extracted, dict) or extracted.get('schema') != 'shieldd-recovery-canonical-row-derivative-v1'
            or extracted.get('metadata_sha256') != digest or not isinstance(extracted.get('slots'), list)
            or len(extracted['slots']) != 2):
        raise relation.RelationError('recovery canonical extraction shape/identity')
    checked = extracted['slots'][slot]
    if not isinstance(checked, dict) or type(checked.get('slot')) is not int or checked['slot'] != slot:
        raise relation.RelationError('recovery canonical extraction slot')
    raw, normalized = arithmetic.normalize_selection(checked, metadata, digest)
    expected, used = _chain(boundaries[slot], raw, normalized)
    if set(raw) != used or any(_json_value(checked.get(key)) != _json_value(value) for key, value in expected.items()):
        raise relation.RelationError('recovery canonical derivative certificate changed')
    if extracted.get('identity') != checked['identity']:
        raise relation.RelationError('recovery canonical outer relation identity')
    m = dict(constant_copy=metadata['constant_copy'], value=((boundaries[slot]['value'], 1),), steps=[])
    for step in expected['steps']:
        m['steps'].append([step['before'], step['left'], {'native': f"{step['right']:064x}"},
                           step['factor'], step['product'], step['after']])
    source, _ = generate_linear_checked(m, checked)
    return source.replace('RuntimeTransferRemainder', f'RuntimeTransferRecovery{slot}Canonical').replace(
        'actual_remainder_canonical', 'actual_randomizer_canonical')
