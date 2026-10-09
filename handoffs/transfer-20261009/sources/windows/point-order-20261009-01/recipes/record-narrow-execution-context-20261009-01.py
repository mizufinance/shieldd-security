from pathlib import Path
import argparse, hashlib, json, subprocess

p = argparse.ArgumentParser()
p.add_argument('--prefix', required=True, choices=['point-trace-composition', 'point-order'])
p.add_argument('--guard-sha256', required=True)
args = p.parse_args()
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
stem = f'windows-{args.prefix}-20261009-01'
guard = diag / ('root-' + stem + '.ps1')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(guard) == args.guard_sha256
assert not (diag / (stem + '-kernel')).exists()
dest = local / f'{args.prefix}-execution-context-20261009-01.json'
assert not dest.exists()
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
lock = (repo / 'shieldd.lock').read_bytes()
assert b'844389ee069e1fb2e576708842d0b389b4d9a44a' in lock
context = {'kind': 'Fresh actual narrow-kernel launch identity; qualification requires later completed guard and audits',
           'batch': stem, 'actual_execution_checkout_head': head,
           'guard_sha256': sha(guard),
           'source_manifest_sha256': sha(diag / (stem + '-source/manifest.json')),
           'shieldd_lock_sha256': hashlib.sha256(lock).hexdigest(),
           'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
           'kernel_run_at_record_creation': False, 'proof_credit_at_record_creation': 0}
dest.write_bytes((json.dumps(context, indent=2) + '\n').encode())
print(json.dumps(context))
