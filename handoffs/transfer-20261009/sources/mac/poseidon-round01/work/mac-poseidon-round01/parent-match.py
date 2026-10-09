"""Match the first registry PARAMS hash to the captured source graph (data only)."""
import argparse
import hashlib
import json
import sqlite3
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--database', type=Path, required=True)
parser.add_argument('--runtime', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
# Exact Scalar modulus; kept explicit for validating the parameter artifact.
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
source = args.runtime / 'crates/crypto/primitives/params/poseidon381-wide.json'
artifact = json.loads(source.read_text())
if (artifact['schema'], int(artifact['modulus']), artifact['alpha'], artifact['full_rounds'], artifact['partial_rounds'], artifact['skip_matrices']) != ('shieldd.poseidon381.v1', P, 5, 8, 57, 0):
    raise ValueError('wrong parameter recipe')
ark = [[int(v, 16) for v in row] for row in artifact['ark']]
mds = [[int(v, 16) for v in row] for row in artifact['mds']]
if len(ark) != 65 or len(mds) != 6 or any(len(row) != 6 for row in ark + mds):
    raise ValueError('wrong parameter shape')
if not all(0 <= v < P for row in ark + mds for v in row):
    raise ValueError('noncanonical parameter')
connection = sqlite3.connect(args.database.resolve().as_uri() + '?mode=ro', uri=True)
node_id, constant_id = 503, 174
consumed_nodes, consumed_constants = [], []


def merge(op, left, right):
    global node_id, constant_id
    if left[0] == right[0] == 'native':
        value = left[1] + right[1] if op == 'add' else left[1] * right[1]
        return ('native', value % P)
    if right[0] == 'native':
        left, right = right, left
    if left[0] == 'native':
        actual = connection.execute('SELECT value FROM constants WHERE id=?', (constant_id,)).fetchone()
        if actual is None or int(actual[0], 16) != left[1]:
            raise ValueError(f'constant mismatch at {constant_id}')
        consumed_constants.append({'id': constant_id, 'value': actual[0]})
        left = (0, constant_id)
        constant_id += 1
    actual = connection.execute('SELECT op,lk,li,rk,ri FROM nodes WHERE id=?', (node_id,)).fetchone()
    expected = (op, left[0], left[1], right[0], right[1])
    if actual != expected:
        raise ValueError(f'node mismatch at {node_id}: {actual} != {expected}')
    consumed_nodes.append([node_id, *actual])
    result = (2, node_id)
    node_id += 1
    return result


def add(a, b): return merge('add', a, b)
def mul(a, b): return merge('mul', a, b)


inputs = [(1, i) for i in [11, 12, 18, 19]]
state = [('native', 4 * 256 + 23)] + [('native', 0)] * 5
for word, inp in enumerate(inputs, 1):
    state[word] = add(state[word], inp)
absorbed = state.copy()
rounds = []
for round_index in range(65):
    start = node_id
    before = state.copy()
    state = [add(value, ('native', constant)) for value, constant in zip(state, ark[round_index])]
    after_ark = state.copy()
    for i, value in enumerate(state):
        if round_index < 4 or round_index >= 61 or i == 0:
            square = mul(value, value)
            state[i] = mul(mul(square, square), value)
    after_sbox = state.copy()
    next_state = []
    for row in mds:
        total = ('native', 0)
        for coefficient, value in zip(row, state):
            total = add(total, mul(('native', coefficient), value))
        next_state.append(total)
    state = next_state
    rounds.append({'round': round_index, 'nodes_inclusive': [start, node_id - 1],
                   'before': before, 'after_ark': after_ark, 'after_sbox': after_sbox, 'after_mds': state.copy()})
node_digest = hashlib.sha256(json.dumps(consumed_nodes, separators=(',', ':')).encode()).hexdigest()
constant_digest = hashlib.sha256(json.dumps(consumed_constants, separators=(',', ':')).encode()).hexdigest()
result = {'kind': 'source-pattern data match only; no kernel/compiler/runtime refinement credit',
          'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
          'call': 'registry::Leaf::hash first PARAMS, arity4, domain23',
          'width': 6, 'domain': 23, 'arity': 4, 'iv': 1047,
          'input_witness_ids': [11, 12, 18, 19], 'absorption_nodes_inclusive': [503, 506],
          'nodes_inclusive': [503, node_id - 1], 'node_count': len(consumed_nodes),
          'constants_inclusive': [174, constant_id - 1], 'constant_count': len(consumed_constants),
          'parameter_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'ordered_matched_node_records_sha256': node_digest,
          'ordered_matched_constant_records_sha256': constant_digest,
          'absorbed_state': absorbed, 'rounds': rounds, 'final_state': state,
          'result': state[1], 'assertion_and_consumer_rows': 'Not yet mapped; full row descriptor remains worker-owned.'}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['rounds', 'absorbed_state', 'final_state']}))
