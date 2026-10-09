from pathlib import Path
import hashlib, json

local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stem = 'windows-graph-input-bridge-20261009-07'
batch = diag / (stem + '-kernel')
out = local / 'windows-header-carrier-20261009-01-packet'
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
write = lambda p, value: p.write_bytes((json.dumps(value, indent=2) + '\n').encode())
assert (batch / 'exit.txt').read_text().strip() == '0'
assert all((batch / n).exists() for n in ['end.txt', 'complete.txt']) and not (batch / 'stop.txt').exists()
assert (diag / 'safe-inverse-boundary-2026100907/resume-status.txt').read_text().strip() == '0'
manifest = load(batch / 'manifest.json')
checks = {}
for name in manifest['order']:
    leaf = batch / name
    audit = load(leaf / 'audit.json')
    assert (leaf / 'exit.txt').read_text().strip() == '0' and (leaf / 'end.txt').exists()
    assert not (leaf / 'stop.txt').exists() and audit['full_types_checked']
    assert audit['audits'] == len(manifest['expected_theorems_by_module'][name])
    assert sha(Path(manifest['sources'][name]['path'])) == audit['original_source_sha256']
    assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in audit['axioms'].values())
    checks[name] = {'audit': audit, 'actual_exit': 0, 'stdout_sha256': sha(leaf / 'stdout.txt'),
                    'stderr_sha256': sha(leaf / 'stderr.txt')}
assert sum(x['audit']['audits'] for x in checks.values()) == 29
out.mkdir()
files = {}
def copy(p, rel):
    target = out / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(p.read_bytes())
    assert sha(p) == sha(target)
    files[rel] = {'sha256': sha(p), 'bytes': p.stat().st_size}
copy(Path(manifest['sources']['TransferCircuitHeaderCarrierSeed']['path']),
     'circuits/ShielddSecurity/TransferCircuitHeaderCarrierSeed.lean')
for p in [local / ('prepare-' + stem + '.py'), local / ('run-safe-' + stem + '.ps1'),
          diag / ('root-' + stem + '.ps1'), diag / ('audit-' + stem + '.py')]:
    copy(p, 'recipes/' + p.name)
copy(batch / 'manifest.json', 'inputs/manifest.json')
runtime = Path('C:/src/shieldd-pr160-844389ee')
receipt = {'runtime_sha': manifest['runtime_sha'], 'scope': manifest['scope'],
    'actual_exit': 0, 'source_manifest_sha256': sha(batch / 'manifest.json'),
    'start': (batch / 'start.txt').read_text().strip(), 'end': (batch / 'end.txt').read_text().strip(),
    'recipe': load(batch / 'recipe.json'), 'new_theorem_audits': 6, 'prerequisite_replay_audits': 23,
    'root_resume_status': 0, 'modules': checks,
    'runtime_source_bindings': {
        'transfer_header': {'path': 'crates/crypto/circuits/src/transfer.rs',
            'sha256': sha(runtime / 'crates/crypto/circuits/src/transfer.rs'), 'lines': [204, 212]},
        'compiler_input_columns': {'path': 'third_party/commonware/cryptography/src/zk/pari/circuit.rs',
            'sha256': sha(runtime / 'third_party/commonware/cryptography/src/zk/pari/circuit.rs'),
            'allocation_lines': [385, 415], 'link_outline_lines': [578, 645]}},
    'instance_parameters': {'input_count': 22735, 'first_private_column': 3,
        'source_blinding_input': 6, 'private_blinding_column': 9, 'committed_column': 2,
        'source_regulated_input': 7, 'private_regulated_column': 10,
        'source_claimed_statement_input': 22734, 'private_claimed_statement_column': 22737,
        'public_column': 1, 'constant_copy_column': 200692},
    'constructed_inputs': 'First eight headers and final claimed statement. Other 22726 gadget inputs remain supplied by their pending owned construction.',
    'local_rows': 'Regulated Boolean, public-to-private statement, committed-to-private blinding, and constant-copy equality.',
    'whole_row_inclusion': 'OPEN: these expected integer coefficient bodies still need exact canonical indexed inclusion in fullRows.',
    'complete_assignment': 'OPEN: materialized compiler outputs/auxiliaries, full Topological/Legal and reverse row coverage remain pending.',
    'full_transfer': 'OPEN', 'native_suites': 'NOT_RUN', 'publication': 'LOCAL_REVIEW_PACKET_ONLY'}
write(out / 'receipt.json', receipt)
files['receipt.json'] = {'sha256': sha(out / 'receipt.json'), 'bytes': (out / 'receipt.json').stat().st_size}
write(out / 'manifest.json', {'files': files, 'full_transfer': 'OPEN'})
print(json.dumps({'packet': str(out), 'manifest_sha256': sha(out / 'manifest.json'),
    'receipt_sha256': sha(out / 'receipt.json'), 'new_theorem_audits': 6, 'full_transfer': 'OPEN'}))
