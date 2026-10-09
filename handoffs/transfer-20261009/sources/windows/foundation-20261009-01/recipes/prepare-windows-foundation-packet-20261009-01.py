from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
src = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')
out = Path('C:/src/shieldd-transfer-handoffs/windows-foundation-20261009-01')
assert not out.exists(), 'fresh packet required'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
modules = {'CompilerGraphEvaluationSoundness': '05',
           'TransferCircuitInputSeed': '05', 'TransferCircuitHeaderInputs': '06'}
checks = []
for suffix in ['05', '06']:
    batch = root / f'windows-graph-input-bridge-20261009-{suffix}-kernel'
    boundary = root / f'safe-inverse-boundary-20261009{suffix}'
    assert all((batch / n).exists() for n in ['end.txt', 'exit.txt', 'complete.txt'])
    assert (batch / 'exit.txt').read_text().strip() == '0' and not (batch / 'stop.txt').exists()
    assert (boundary / 'resume-status.txt').read_text().strip() == '0'
    manifest = load(batch / 'manifest.json')
    leaves = {}
    for name in manifest['order']:
        leaf = batch / name
        audit = load(leaf / 'audit.json')
        assert (leaf / 'exit.txt').read_text().strip() == '0' and (leaf / 'end.txt').exists()
        assert not (leaf / 'stop.txt').exists()
        assert audit['full_types_checked'] and audit['audits'] == len(manifest['expected_theorems_by_module'][name])
        assert audit['original_source_sha256'] == sha(src / (name + '.lean'))
        assert all(set(used) <= {'propext', 'Classical.choice', 'Quot.sound'} for used in audit['axioms'].values())
        leaves[name] = {'audit': audit, 'actual_exit': 0,
                        'stdout_sha256': sha(leaf / 'stdout.txt'),
                        'stderr_sha256': sha(leaf / 'stderr.txt')}
    checks.append({'local_batch': str(batch), 'manifest_sha256': sha(batch / 'manifest.json'),
                   'recipe': load(batch / 'recipe.json'), 'actual_exit': 0,
                   'start': (batch / 'start.txt').read_text().strip(),
                   'end': (batch / 'end.txt').read_text().strip(),
                   'root_resume_status': 0, 'scope': manifest['scope'], 'leaves': leaves})
runtime = Path('C:/src/shieldd-pr160-844389ee')
runtime_sha = subprocess.check_output(['git', '-C', str(runtime), 'rev-parse', 'HEAD'], text=True).strip()
assert runtime_sha == '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert not subprocess.check_output(['git', '-C', str(runtime), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
out.mkdir()
files = {}
for name, suffix in modules.items():
    path = src / (name + '.lean')
    target = out / 'circuits/ShielddSecurity' / path.name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(path.read_bytes())
    assert sha(path) == sha(target)
    files[str(target.relative_to(out)).replace('\\', '/')] = {'sha256': sha(target), 'bytes': target.stat().st_size,
        'imports': re.findall(r'^import\s+([\w.]+)', path.read_text(), re.M), 'actual_check_suffix': suffix}
runtime_source = runtime / 'crates/crypto/circuits/src/transfer.rs'
receipt = {'runtime_sha': runtime_sha, 'runtime_tracked_clean': True,
    'runtime_header_source_sha256': sha(runtime_source), 'runtime_header_source_lines': [204, 212],
    'unique_new_theorem_audits': 13, 'checks': checks,
    'proof_credit': 'Symbolic compiler evaluation, reserved input seed, and eight-input header codec only.',
    'open': ['Concrete full source graph identity and all node/assertion certificates',
             'Concrete full-row coverage, including indexed owned range rows',
             'Graph-to-independent TransferSem and LocalRowSoundness',
             'Remaining 22727 raw gadget input allocations',
             'Concrete Topological and Legal derivations and reverse emitted-row coverage',
             'Complete circuit assignment and Rust constructor correspondence',
             'Concrete deployed Crypto and canonical field interpretation',
             'Native proof admission and durable state closure'],
    'wire_distinction': {'source_input_6': 'balance_blinding', 'private_column': 9,
                         'committed_column': 2, 'link_row_index': 200768,
                         'constant_copy_column': 200692,
                         'note': 'Exact full graph/row bindings remain instance obligations; source input indices are not compiler columns.'},
    'preserved_failures': [{'suffix': '03', 'cause': 'Reserved identifier in handwritten seed source', 'proof_credit': 0, 'semantic_control_credit': 0},
                           {'suffix': '04', 'cause': 'Nested conjunction projection in handwritten seed proof', 'proof_credit': 0, 'semantic_control_credit': 0}],
    'dependency_transport': 'Existing maintained-review-20261009-01 source inventory and kernel-pilot-20261009-01 source closure; this packet adds only three handwritten modules.',
    'publication_base_observed': '0659fe446c0554fe296b6f97b78b1fd90f54714f',
    'publication_status': 'LOCAL_REVIEW_PACKET_ONLY', 'full_transfer': 'OPEN', 'native_suites': 'NOT_RUN'}
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
files['receipt.json'] = {'sha256': sha(out / 'receipt.json'), 'bytes': (out / 'receipt.json').stat().st_size}
(out / 'manifest.json').write_text(json.dumps({'files': files, 'full_transfer': 'OPEN'}, indent=2) + '\n')
print(json.dumps({'packet': str(out), 'manifest_sha256': sha(out / 'manifest.json'),
                  'receipt_sha256': sha(out / 'receipt.json'), 'unique_new_audits': 13, 'full_transfer': 'OPEN'}))
