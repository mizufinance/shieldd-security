from pathlib import Path
import hashlib, json
root = Path('C:/src/shieldd-pr160-844389ee')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
paths = [
 'crates/core/app/src/action_handler/transaction.rs',
 'crates/core/app/src/app/delivery.rs',
 'crates/core/app/src/app/lifecycle.rs',
 'crates/core/app/src/app/mod.rs',
 'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
]
original = Path('C:/src/shieldd-transfer-handoffs/windows-native-backlog-20261009-01.json')
result = {
 'schema': 'windows-native-state-boundary-alignment-v1',
 'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
 'original_backlog_sha256': sha(original),
 'source_files': {p: sha(root / p) for p in paths},
 'evidence_kind': 'source review only; no runtime test, refinement, or defect conclusion',
 'obligations': [
  'transfer_execute_validated can return an error after writes to the supplied StateWrite; per-action rollback is not its unconditional contract.',
  'Delivery uses an exclusive StateDelta and applies it only after execution and per-transaction index work succeed; errors before apply discard this delta.',
  'Deferred transaction queue append occurs after StateDelta.apply.',
  'Deferred flush drains the queue via mem::take before fallible index writes; failure can preserve already pending effects while draining the queue. Do not assume unconditional queue restoration.',
  'end_block expects successful deferred flush and can panic before component hooks when flush fails.',
  'G5 replay and refinement must target the actual caller, abort boundary and durable-store behavior.',
 ],
 'native_successors': 'UNRUN; existing predecessor gates unchanged',
 'full_transfer': 'OPEN',
}
out = Path('C:/src/shieldd-transfer-handoffs/windows-native-state-boundary-alignment-20261009-01.json')
assert not out.exists()
out.write_bytes((json.dumps(result, indent=2) + '\n').encode())
print(json.dumps({'path': str(out), 'sha256': sha(out)}))
