"""Exact retained RNK reciprocal rows and a three-write completion footprint.

This is an additive consumer of accepted RNK metadata and retained ordinary-row
selections. It performs no ordinary replay and grants no qualification. Native
input legality and the same accepted SDK scalar remain independently derived
constructor inputs; output nonzero and row satisfaction are not plan premises.
"""
from . import transfer_ownership as owner


def plan(checked, extracted, sequence):
    """Retain the actual inverse/product/assertion/copy equations exactly."""
    try:
        return _plan(checked, extracted, sequence)
    except (KeyError, TypeError, IndexError, AttributeError) as error:
        raise owner.relation.RelationError('RNK inverse typed accepted inputs') from error


def _plan(checked, extracted, sequence):
    from .generate_transfer_rnk_sparse_sequence import _validate
    # Reuse the maintained soundness boundary's exact actual-row acceptance.
    # Its generated source is discarded: this call is structural validation,
    # not a proof receipt or a substitute for the ordinary replay.
    owner.generate_rnk_inverse_boundary(checked, extracted)
    _validate(sequence)
    if sequence['identity'] != extracted['identity'] or any(
            checked['metadata'][key] != sequence['identity'][other]
            for key, other in (('relation_digest', 'relation_digest'),
                               ('domain_size', 'domain_size'),
                               ('full_rows', 'stored_rows'))):
        raise owner.relation.RelationError('RNK inverse exact same original relation')
    def observed(value):
        return checked['derived'][value[1]] if value[0] == 'source' else \
            owner.canonical([(0, value[1])])
    def unit(lc):
        if len(lc) != 1 or lc[0][1] != 1:
            raise owner.relation.RelationError('RNK inverse exact unit owned pivot')
        return lc[0][0]
    x, y = map(observed, checked['points']['output'])
    inverse = observed(checked['nonidentity_inverse'])
    pair = next(value for value in extracted['products'] if value['role'] == 'nonidentity')
    records = {value['row']: value for value in extracted['selected_rows']}
    minus, plus, equality = [records[index] for index in pair['rows']]
    auxiliary = tuple((column, int(value, 16)) for column, value in minus['b'])
    plus_lc = tuple((column, int(value, 16)) for column, value in plus['b'])
    output = owner.canonical((column, value * pow(4, -1, owner.relation.MODULUS))
        for column, value in owner.combine(plus_lc, auxiliary, -1))
    copy = checked['metadata']['constant_copy']
    copied_lc = owner.canonical([(0, 1), (copy, -1)])
    copied = [value for value in records.values() if value['b'] == [] and
        tuple((column, int(coefficient, 16)) for column, coefficient in value['a']) == copied_lc]
    if len(copied) != 1:
        raise owner.relation.RelationError('RNK inverse unique original copy row')
    roles = dict(x=unit(x), y=unit(y), inverse=unit(inverse),
                 product=unit(output), auxiliary=unit(auxiliary), copy=copy)
    observed_output = [tuple((owner.relation.natural(column, sequence['domain_size']),
        owner.relation.natural(value, owner.relation.MODULUS)) for column, value in lc)
        for lc in sequence['observed_output']]
    if (roles['x'], roles['y']) != (3763, 3764) or observed_output != [x, y]:
        raise owner.relation.RelationError('RNK inverse exact observed native DH output')
    writes = [roles[key] for key in ('inverse', 'product', 'auxiliary')]
    if len(set(writes)) != 3 or set(writes) & {0, roles['x'], roles['y'], copy}:
        raise owner.relation.RelationError('RNK inverse fresh distinct three-write layout')
    if set(writes) & set(sequence['target_writes']) or \
            set(writes) & set(sequence['protected_columns']):
        raise owner.relation.RelationError('RNK inverse whole window/write consumer exclusion')
    for block in sequence['row_blocks']:
        for row in block['target_rows']:
            if any(column in writes for column, _ in row['a'] + row['b']):
                raise owner.relation.RelationError('RNK inverse all126 original-row support exclusion')
    return dict(schema='shieldd-transfer-rnk-inverse-completion-plan-v1',
        identity=sequence['identity'], roles=roles, writes=writes,
        rows=[minus, plus, equality, copied[0]],
        prior_blocks=134, windows=126,
        scope='exact four retained rows and three-write exclusion only; native legality, construction, caller and full Transfer remain separate')
