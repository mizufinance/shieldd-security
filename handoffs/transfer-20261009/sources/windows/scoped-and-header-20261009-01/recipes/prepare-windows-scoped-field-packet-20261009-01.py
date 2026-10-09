from pathlib import Path
import hashlib, json, re

local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
batch = diag / 'windows-scoped-field-knowledge-20261009-02-kernel'
out = local / 'windows-scoped-field-knowledge-20261009-02-packet'
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
write = lambda p, m: p.write_bytes((json.dumps(m, indent=2) + '\n').encode())
assert (batch / 'exit.txt').read_text().strip() == '0'
assert (batch / 'complete.txt').exists() and (batch / 'end.txt').exists() and not (batch / 'stop.txt').exists()
assert (diag / 'safe-scoped-field-boundary-2026100902/resume-status.txt').read_text().strip() == '0'
manifest = load(batch / 'manifest.json')
audits = {}
for name in manifest['order']:
    leaf = batch / name
    audit = load(leaf / 'audit.json')
    assert audit['audits'] == len(manifest['expected_theorems_by_module'][name]) and audit['full_types_checked']
    assert (leaf / 'exit.txt').read_text().strip() == '0' and (leaf / 'end.txt').exists()
    assert not (leaf / 'stop.txt').exists()
    assert audit['original_source_sha256'] == sha(Path(manifest['sources'][name]['path']))
    assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in audit['axioms'].values())
    audits[name] = {'audit': audit, 'actual_exit': 0, 'stdout_sha256': sha(leaf / 'stdout.txt'),
                    'stderr_sha256': sha(leaf / 'stderr.txt')}
assert sum(v['audit']['audits'] for v in audits.values()) == 251
out.mkdir()
files = {}
def copy(p, rel):
    target = out / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(p.read_bytes())
    assert sha(target) == sha(p)
    files[rel] = {'sha256': sha(p), 'bytes': p.stat().st_size}
copy(Path(manifest['sources']['TransferScopedFieldClaimAcceptance']['path']),
     'circuits/ShielddSecurity/TransferScopedFieldClaimAcceptance.lean')
for p in [local / 'prepare-windows-scoped-field-knowledge-20261009-02.py',
          local / 'run-safe-windows-scoped-field-knowledge-20261009-02.ps1',
          diag / 'root-windows-scoped-field-knowledge-20261009-02.ps1',
          diag / 'audit-windows-scoped-field-knowledge-20261009-02.py']:
    copy(p, 'recipes/' + p.name)
copy(batch / 'manifest.json', 'inputs/manifest.json')
source = (out / 'circuits/ShielddSecurity/TransferScopedFieldClaimAcceptance.lean').read_text(encoding='utf-8-sig')
assert 'item.family = input.family → relation = input.key.key.relationDigest →' in source
assert 'first.item.family = input.family → relation = input.key.key.relationDigest →' in source
assert 'facts.2.1.2.1 _ _ facts.2.2.1' in source
receipt = {'runtime_sha': manifest['runtime_sha'], 'scope': manifest['scope'],
    'actual_exit': 0, 'source_manifest_sha256': sha(batch / 'manifest.json'),
    'recipe': load(batch / 'recipe.json'), 'root_resume_status': 0,
    'start': (batch / 'start.txt').read_text().strip(), 'end': (batch / 'end.txt').read_text().strip(),
    'fresh_modules': 26, 'root_audits': 9, 'root_public_theorems': 6,
    'root_definition_constructor_audits': 3, 'dependency_replay_audits': 242,
    'root_audits_are_not_nine_new_theorems': True, 'modules': audits,
    'original_mac_source_sha256': manifest['original_mac_source_sha256'],
    'original_mac_source_preserved': True, 'successor_module': 'TransferScopedFieldClaimAcceptance',
    'owned_range_bridge': 'OwnedRange is definitionally the same predicate as the existing field bridge. The M17 indexed_owned_range result can supply this predicate; concrete IndexedCoverage and LocalRowSoundness remain open.',
    'preflight_failure': {'recipe_sha256': sha(local / 'prepare-windows-scoped-field-knowledge-20261009-01.py'),
        'cause': 'Overbroad source preflight matched the word opaque in a TransferTransaction documentation comment.',
        'kernel_started': False, 'proof_credit': 0, 'semantic_control_credit': 0},
    'deployed_instance': 'Crypto/codec, SDK extraction, complete rows/public/committed expressions and native/state correspondence remain required.',
    'full_transfer': 'OPEN', 'publication': 'LOCAL_REVIEW_PACKET_ONLY'}
write(out / 'receipt.json', receipt)
files['receipt.json'] = {'sha256': sha(out / 'receipt.json'), 'bytes': (out / 'receipt.json').stat().st_size}
write(out / 'manifest.json', {'files': files, 'full_transfer': 'OPEN'})
print(json.dumps({'packet': str(out), 'manifest_sha256': sha(out / 'manifest.json'),
    'receipt_sha256': sha(out / 'receipt.json'), 'root_audits': 9, 'dependency_replay_audits': 242}))
