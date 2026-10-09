"""Owned encryption key-selector source shape; Boolean/row meaning is separate."""
from . import poseidon_graph, transfer_relation as relation


def expected_selection(flag, detection, payload):
    """Independent `payload + flag * (detection - payload)` Var source graph.

    Native folding, circuit constant folding, and native operand reordering
    follow the exact pinned Var ABI already used by owned loop templates.
    """
    nodes, natives, inputs = [], [], []

    def put(node, native=False):
        nodes.append(node)
        natives.append(native)
        return len(nodes) - 1

    def constant(value, native=False):
        return put(dict(kind='constant', value=value % relation.MODULUS), native)

    def observed(value):
        if value[0] == 'native':
            return constant(value[1], True)
        if value[0] != 'source':
            raise relation.RelationError('DH selection observed kind')
        node = put(dict(kind='input', slot=len(inputs)))
        inputs.append(value[1])
        return node

    def op(kind, left, right):
        if nodes[left]['kind'] == nodes[right]['kind'] == 'constant':
            a, b = nodes[left]['value'], nodes[right]['value']
            return constant(a + b if kind == 'add' else a * b, natives[left] and natives[right])
        if natives[right] and not natives[left]:
            left, right = right, left
        return put(dict(kind=kind, left=left, right=right))

    f, yes, no = map(observed, (flag, detection, payload))
    negated = (constant(-nodes[no]['value'], natives[no]) if nodes[no]['kind'] == 'constant'
               else op('mul', constant(-1), no))
    difference = op('add', yes, negated)
    product = op('mul', f, difference)
    output = op('add', no, product)
    return dict(arity=len(inputs), nodes=nodes, output=output), inputs


def match_selection(checked):
    """Verify unconditional detection or both selected-key coordinate cones."""
    role = checked['metadata']['role']
    bindings, base = checked['bindings'], checked['points']['base']
    if role == 0:
        if base != bindings['detection_key']:
            raise relation.RelationError('DH unconditional detection source mismatch')
        return dict(role=0, cones=[], scope='Exact unconditional detection operand; curve/native/caller semantics OPEN')
    if type(role) is not int or not 1 <= role <= 4:
        raise relation.RelationError('DH selected-key occurrence outside four tiers')

    def name(handle):
        return 'cwn'[handle[0]] + str(handle[1])

    source = {}
    for handle, terms in checked['expressions'].items():
        if handle[0] == 0:
            source[name(handle)] = dict(kind='constant', value=terms[0][1] if terms else 0)
        elif handle[0] == 1:
            source[name(handle)] = dict(kind='witness')
    for handle, (multiply, left, right) in checked['nodes'].items():
        source[name(handle)] = dict(kind='mul' if multiply else 'add', left=name(left), right=name(right))
    cones = []
    for axis in range(2):
        graph, inputs = expected_selection(bindings['flagged'], bindings['detection_key'][axis], bindings['payload_key'][axis])
        output = base[axis]
        if output[0] == 'native':
            if graph['arity'] or graph['nodes'][graph['output']] != dict(kind='constant', value=output[1]):
                raise relation.RelationError('DH selected native base source mismatch')
            pairs = []
        else:
            try:
                pairs = poseidon_graph.match_source(graph, source, list(map(name, inputs)), name(output[1]))
            except ValueError as error:
                raise relation.RelationError('DH selected key source mismatch: ' + str(error)) from error
        cones.append(dict(axis=axis, graph=graph, inputs=inputs, output=output, pairs=pairs))
    return dict(role=role, cones=cones,
                scope='Exact two-coordinate key selector source shape; Boolean/actual-row/curve/native/caller proof OPEN')
