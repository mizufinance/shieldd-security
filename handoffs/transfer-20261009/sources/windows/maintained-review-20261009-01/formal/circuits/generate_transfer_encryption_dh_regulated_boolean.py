"""Render the actual Boolean row of the inferred common key-selector input.

The source candidate's correspondence to the Transfer regulated caller flag is
a separate obligation. This only proves Booleanity of its exact captured LC.
"""
from . import generate_transfer_encryption_dh_boolean as boolean
from .transfer_encryption_dh_boolean import flag_plan, attach_rows
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .transfer_balance_rows import canonical
from . import transfer_relation as relation


def generate(checked, extracted):
    if checked.get('metadata', {}).get('role') != 0:
        raise relation.RelationError('DH common regulated Boolean first-role source required')
    inferred = infer_regulated_selectors(checked)
    regulator = inferred['regulated_candidate']
    if regulator[0] != 'source' or regulator[1][0] != 1:
        raise relation.RelationError('DH regulated Boolean exact witness source required')
    # This is a new arithmetic view of the checked operands, not rewritten
    # observer metadata or qualification. Its plan is rechecked against the
    # original selected physical row and real constant-copy link by the shared
    # renderer. A Rust Bool type or desired branch value supplies no proof.
    view = dict(checked, bindings=dict(checked['bindings'], flagged=regulator))
    candidate = flag_plan(view)
    if len(candidate['steps']) != 1 or candidate['steps'][0]['kind'] != 'assert':
        raise relation.RelationError('DH regulated Boolean one original input assertion required')
    copy = checked['metadata']['constant_copy']
    wanted = canonical((copy if c == 0 else c, v) for c, v in candidate['steps'][0]['terms'])
    reverse = canonical((c, -v) for c, v in wanted)
    matches = []
    for row in extracted.get('selected_rows', []):
        for side in ('a', 'b'):
            relation.terms(row[side], checked['metadata']['domain_size'])
        a, b = (tuple((c, int(v, 16)) for c, v in row[side]) for side in ('a', 'b'))
        if a in (wanted, reverse) and b == wanted:
            matches.append(row['row'])
    if not matches:
        raise relation.RelationError('DH regulated Boolean original physical assertion missing')
    # The generic root label differs from its original nested input label.
    # Propose the label only after checking the exact physical square row;
    # the shared renderer rechecks the row bytes and constant-copy identity.
    selected = dict(extracted, templates=[*extracted['templates'],
                    dict(row=min(matches), roles=['flagged.boolean'])])
    plan = attach_rows(candidate, selected)
    if len(plan['steps']) != 1 or plan['steps'][0]['kind'] != 'assert':
        raise relation.RelationError('DH regulated Boolean one original input assertion required')
    selected['flag_boolean'] = plan
    old_name, source = boolean.generate(view, selected)
    name = 'RuntimeTransferEncryptionRegulatedFlag'
    assert old_name == 'RuntimeTransferEncryptionDh0Flag'
    # Rename inside the maintained producer before its fresh output is saved.
    # No already-generated source or evidence is edited.
    return name, source.replace(old_name, name)
