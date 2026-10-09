from pathlib import Path
import hashlib, json
descriptor = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/receipts/mac/mac-subgroup-descriptor01/subgroup01.json')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(descriptor) == '72cfd5fb64d080f1c1a96414c147de712091fd7a1bf93140ab7fd1172523e573'
data = json.loads(descriptor.read_text())
def local(ref):
    kind, ordinal = ref
    if kind == 0: return ordinal + 7
    if kind == 1:
        assert 11 <= ordinal <= 17
        return ordinal - 11
    assert kind == 2 and 1 <= ordinal <= 58
    return ordinal + 21
curve = [('mul', 2, 2), ('mul', 3, 3), ('mul', 8, 22), ('add', 23, 24),
         ('mul', 7, 22), ('mul', 26, 23), ('add', 9, 27)]
expected = list(curve)
for phase in range(3):
    start = 29 + 17 * phase
    x = 2 if phase == 0 else 25 + 17 * phase
    y = 3 if phase == 0 else 28 + 17 * phase
    expected += [('mul', x, x), ('mul', y, y), ('mul', start, start + 1),
        ('mul', start + 2, 7), ('add', 10 + 4 * phase, start + 3),
        ('mul', 11 + 4 * phase, start + 3), ('add', 12 + 4 * phase, start + 5),
        ('mul', start + 4, start + 6), ('mul', start + 7, 4 + phase),
        ('mul', x, y), ('mul', y, x), ('add', start + 9, start + 10),
        ('mul', start + 11, start + 6), ('mul', start + 12, 4 + phase),
        ('add', start + 1, start), ('mul', start + 14, start + 4),
        ('mul', start + 15, 4 + phase)]
assert len(expected) == len(data['nodes']) == 58
for ordinal, (node, shape) in enumerate(zip(data['nodes'], expected), 1):
    assert node['source_node'] == ordinal
    assert (node['operation'], local(node['left']), local(node['right'])) == shape, ordinal
constants = data['constants']
assert [c['source_constant'] for c in constants] == list(range(15))
modulus = int(data['modulus'])
d = constants[0]['integer']
for ordinal, item in enumerate(constants):
    assert item['integer'] == (d if ordinal == 0 else modulus - 1 if ordinal in [1, 4, 8, 12] else 1)
pairs = [(local(a['certificate']['left']), local(a['certificate']['right'])) for a in data['assertions']]
assert pairs == [(25,28), (13,37), (17,54), (21,71), (0,76), (1,79)]
out = Path('C:/src/shieldd-transfer-handoffs/subgroup-template-layout-check-20261009-01.json')
assert not out.exists()
out.write_bytes((json.dumps({'descriptor_sha256': sha(descriptor), 'checked_arithmetic_nodes': 58,
    'checked_input_leaves': 7, 'checked_constant_leaves': 15, 'checked_assertions': 6,
    'script_sha256': sha(Path(__file__)), 'result': 'PASS',
    'evidence_kind': 'independent finite source-data layout comparison only; no Lean kernel or semantic proof credit',
    'generic_lean_template': 'GroupSubgroupSourceGraph.lean; currently under development',
    'full_transfer': 'OPEN'}, indent=2) + '\n').encode())
print(json.dumps({'path': str(out), 'sha256': sha(out)}))
