"""Bounded source candidates for the two regulated key selectors.

Actual caller/parameter identities, Boolean rows, cofactor membership and native
readers remain required. Source shape never certifies those semantic roles.
"""
from . import transfer_relation as relation
from .transfer_encryption_dh_selection import match_selection


def infer_regulated_selectors(checked):
    if checked.get('qualified') is not True:
        raise relation.RelationError('DH key selector qualified source required')
    nodes, derived = checked['nodes'], checked['derived']

    def native(handle):
        if handle[0] != 0:
            return None
        terms = derived[handle]
        if not terms:
            return 0
        if len(terms) == 1 and terms[0][0] == 0:
            return terms[0][1]
        raise relation.RelationError('DH key selector nonconstant source leaf')

    def axis(output):
        if output[0] != 'source' or output[1] not in nodes or nodes[output[1]][0]:
            raise relation.RelationError('DH regulated key selector must have captured add root')
        _, a, b = nodes[output[1]]
        candidates = []
        for fallback, product in ((a, b), (b, a)):
            value = native(fallback)
            if value is None or product not in nodes or not nodes[product][0]:
                continue
            _, left, right = nodes[product]
            for flag, difference in ((left, right), (right, left)):
                if flag[0] != 1 or difference not in nodes or nodes[difference][0]:
                    continue
                _, x, y = nodes[difference]
                for leaf, negative in ((x, y), (y, x)):
                    if leaf[0] == 1 and native(negative) == (-value) % relation.MODULUS:
                        candidates.append((('source', flag), ('source', leaf), ('native', value)))
        if len(candidates) != 1:
            raise relation.RelationError('DH regulated key selector must have one exact bounded candidate')
        return candidates[0]

    result = {}
    flags = []
    for name in ('detection_key', 'payload_key'):
        parsed = [axis(value) for value in checked['bindings'][name]]
        if parsed[0][0] != parsed[1][0]:
            raise relation.RelationError('DH regulated key coordinate flags disagree')
        flag = parsed[0][0]
        flags.append(flag)
        leaf = tuple(item[1] for item in parsed)
        fallback = tuple(item[2] for item in parsed)
        view = dict(checked, metadata={'role': 1},
                    bindings=dict(flagged=flag, detection_key=leaf, payload_key=fallback),
                    points={'base': checked['bindings'][name]})
        # Independent expected source builder checks native folding/ordering;
        # the structural search above only proposes its boundary operands.
        source = match_selection(view)
        result[name] = dict(flag=flag, leaf=leaf, fallback=fallback,
                            output=checked['bindings'][name], cones=source['cones'])
    if flags[0] != flags[1]:
        raise relation.RelationError('DH detection/payload regulated flags disagree')
    return dict(regulated_candidate=flags[0], selectors=result,
                scope='Exact nested regulated-selector source candidates; actual caller/parameter/Boolean/cofactor/native/kernel roles OPEN')
