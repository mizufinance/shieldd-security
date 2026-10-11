"""Pin the runtime primitives behind the endpoint's explicitly open contracts."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
RUNTIME = Path('C:/src/shieldd-pr160-844389ee')
SHA = '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert subprocess.check_output(['git', '-C', str(RUNTIME), 'rev-parse', 'HEAD']).decode().strip() == SHA
assert not subprocess.check_output(['git', '-C', str(RUNTIME), 'status', '--porcelain'])
SELECTION = [
    ('crates/crypto/circuits/src/group.rs', 'ca75207acfd6bcb794f9f54b8ab3f52b236478f6b10761d459747dcbb9155971', 'Native point reader and authorization arithmetic'),
    ('crates/crypto/circuits/src/encoding.rs', 'e675091f22c32999ccdbee7428a1bf8cd6a650dd6d2719556f8bb395ff783a3f', 'Native coordinate encoding'),
    ('crates/crypto/circuits/src/scalar.rs', '4ef5601b479c9888d46ef4040aa0e583186a72ad0a31039029e1edd654b132d5', 'Native scalar operations'),
    ('crates/crypto/primitives/src/generators.rs', 'b16f348693412a19eada6da78550575babcf11f563036b49e16dbcc91a8470fc', 'Scalar-one SpendAuth generator construction'),
    ('crates/crypto/primitives/src/encoding.rs', '922b527349d4372f542cb16a7de3d1ca118f2dd7d443bc0cc03edbfb238f3b7a', 'Compressed point admission'),
    ('crates/core/component/shielded-pool/src/pari.rs', '29aae3aa0835b014b5611d419d42f10128bad89993b6f2a45d4849439c8ee534', 'Actual private scalar and key adapters'),
    ('crates/core/component/shielded-pool/src/transfer/plan.rs', 'b7da6ef17015d845b558aa78c8f7744e7dec55f527b096efd1a65d5df992accd', 'Production verification-key randomization'),
    ('third_party/commonware/cryptography/src/bls12381/primitives/group.rs', 'dafee3e8845a86e9862770681ff60ceefa201c1557695e15578738dad63bd720', 'Scalar conversion and FFI reader'),
]
entries = []
for relative, expected, role in SELECTION:
    data = (RUNTIME / relative).read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected, relative
    target = ROOT / 'runtime-context' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    target.write_bytes(data)
    entries.append({'relative_path': relative, 'bytes': len(data), 'sha256': expected, 'role': role})
assert not subprocess.check_output(['git', '-C', str(RUNTIME), 'status', '--porcelain'])
manifest = {'runtime_sha': SHA, 'runtime_clean': True, 'files': entries,
            'scope': 'Source identity and review context for open primitive contracts; hashes do not establish semantic correspondence.',
            'semantic_correspondence_credit': 0, 'runtime_test_credit': 0,
            'bounded_model_check_credit': 0, 'negative_control_credit': 0, 'certification': False}
(ROOT / 'runtime-context.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({'source_files': len(entries), 'source_bytes': sum(e['bytes'] for e in entries), 'semantic_credit': 0}))
