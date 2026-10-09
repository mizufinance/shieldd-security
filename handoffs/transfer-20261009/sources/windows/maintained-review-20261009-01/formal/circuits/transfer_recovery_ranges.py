"""Captured recovery randomizer Boolean/reconstruction rows, one slot at a time.

This proves a252-bit range, not the stricter subgroup ORDER-1 comparator. Native
canonicality, EPK/DH multiplication and surrounding-row preservation remain
separate obligations. The existing74 roles suffice; no new runtime hook is used.
"""
import hashlib
from . import transfer_recovery_capsule as recovery, transfer_relation as relation
from . import transfer_arithmetic as arithmetic
from .transfer_balance_rows import canonical, combine
from .transfer_note_ranges import _generate_boundary


def boundary(data, output_data, accepted_roles, slot):
    slot = relation.natural(slot, 2)
    checked = recovery.inspect_metadata(data, output_data, accepted_roles)
    capsule = checked['capsules'][slot]
    value = capsule['randomizer']; columns = capsule['bits']
    if len(value) != 1 or value[0][1] != 1:
        raise relation.RelationError('recovery range exact randomizer unit witness')
    if columns != list(range(columns[0], columns[0] + 252)) or value[0][0] in columns:
        raise relation.RelationError('recovery range private bit layout')
    return dict(checked=checked, columns=columns, value=value[0][0], width=252,
                weighted=canonical((c, 2**i) for i, c in enumerate(columns)), slot=slot, kind='randomizer')


def extract(data, stream, output_data, accepted_roles, slot):
    selected = boundary(data, output_data, accepted_roles, slot)
    obj = selected['checked']['metadata']; copy = obj['constant_copy']
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy']}
    for i, c in enumerate(selected['columns']):
        required[(((c, 1),), ((c, 1),))] = ['bit.' + str(i)]
    required[(combine(selected['weighted'], ((selected['value'], 1),), -1), ())] = ['reconstruction']
    result = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                          required, [], [], label='recovery-randomizer252')
    result.update(metadata_sha256=hashlib.sha256(data).hexdigest(), slot=slot, kind='randomizer',
                  scope='one actual recovery252 range; ORDER-1 comparator and native/group joins open')
    return result


def generate(data, extracted, output_data, accepted_roles, slot):
    selected = boundary(data, output_data, accepted_roles, slot)
    obj = selected['checked']['metadata']
    owned = {tuple(h) for h in obj['capsules'][slot]['bits']}
    source = _generate_boundary(data, extracted, accepted_roles, selected, slot, 'randomizer', owned,
                               f'RuntimeTransferRecovery{slot}RandomizerRange')
    return source.replace('-- Actual range role only; shared hash/tree construction is separate.',
                          '-- Actual recovery252 range only; ORDER-1 comparator, EPK/DH and native joins remain separate.')
