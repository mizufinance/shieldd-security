"""Bounded Boolean derivation plans for captured DH flags.

A plan is source algebra plus actual Boolean/product row obligations. It is
not a kernel theorem or a claim about the meaning of the volume flag.
"""
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def flag_plan(checked):
    value = checked['bindings']['flagged']
    if value[0] == 'native':
        if value[1] not in (0, 1):
            raise relation.RelationError('DH native flag is not Boolean')
        return dict(root=None, native=value[1], steps=[])
    root = value[1]
    nodes, derived = checked['nodes'], checked['derived']
    one = ((0, 1),)
    choices = {}

    def choice(source):
        lc = derived[source]
        if lc in ((), one):
            return ('constant', (), 0 if not lc else 1)
        node = nodes.get(source)
        if node is not None:
            multiply, left, right = node
            if not multiply:
                for const, negative in ((left, right), (right, left)):
                    neg = nodes.get(negative)
                    if derived[const] != one or neg is None or not neg[0]:
                        continue
                    for factor, child in ((neg[1], neg[2]), (neg[2], neg[1])):
                        if (derived[factor] == ((0, relation.MODULUS - 1),) and
                                lc == combine(one, derived[child], -1)):
                            return ('not', (child,), None)
            else:
                for const, child in ((left, right), (right, left)):
                    if derived[const] == one and lc == derived[child]:
                        return ('alias', (child,), None)
                if left[0] != 0 and right[0] != 0:
                    return ('and', (left, right), 'node.' + str(source[1]))
        # BoolVar::assert may constrain an arbitrary affine LC, such as
        # proof_context - 1. Do not replace this actual row by a witness row.
        return ('assert', (), 'flagged.boolean' if source == root else
                'flagged.input.' + str(source[0]) + '.' + str(source[1]))

    pending = [root]
    while pending:
        source = pending.pop()
        if source in choices:
            continue
        if len(choices) >= 8192:
            raise relation.RelationError('DH Boolean plan bound')
        choices[source] = choice(source)
        pending.extend(choices[source][1])
    steps = [dict(source=source, terms=canonical(derived[source]), kind=kind,
                  inputs=inputs, obligation=obligation)
             for source, (kind, inputs, obligation) in sorted(choices.items())]
    return dict(root=root, native=None, steps=steps)


def attach_rows(plan, extracted):
    """Resolve every obligation to rows already recovered from the full replay."""
    templates = {role: item['row'] for item in extracted['templates'] for role in item['roles']}
    products = {item['role']: item['rows'] for item in extracted['products']}
    steps = []
    for item in plan['steps']:
        role = item['obligation']
        if item['kind'] == 'assert':
            if role not in templates:
                raise relation.RelationError('DH Boolean input row missing')
            rows = [templates[role]]
        elif item['kind'] == 'and':
            if role in products:
                rows = products[role]
            elif role + '.square' in templates:
                rows = [templates[role + '.square']]
            else:
                raise relation.RelationError('DH Boolean product rows missing')
        else:
            rows = []
        steps.append(dict(item, rows=rows))
    return dict(plan, steps=steps,
                scope='Captured Boolean algebra and actual row obligations; kernel/volume semantics OPEN')
