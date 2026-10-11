"""Read-only preservation and exact runtime identity checkpoint; no certification."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parent
MAIN = Path('C:/src/shieldd-formal')
DIAG = ROOT.parent
RUNTIME = Path('C:/src/shieldd-pr160-844389ee')
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
baseline = DIAG / 'transfer-prerequisite-floor-20261010-01/preservation-baseline.json'
d = json.loads(baseline.read_text())
for r in d['protected'] + d['foreign']: assert pin(r['path']) == r
env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
def git(repo, *args):
    return subprocess.check_output(['git', '-c', 'core.fsmonitor=false', *args], cwd=repo, env=env)
mainHead = git(MAIN, 'rev-parse', 'HEAD').decode().strip()
mainStatus = git(MAIN, 'status', '--porcelain=v1', '-z', '--untracked-files=all')
assert mainHead == 'b0f7e8b885dc0c13ee3bd5c82851afb690f48d48'
assert len(mainStatus) == 66913 and hashlib.sha256(mainStatus).hexdigest() == '73b97fd68a818d46e9d9979d98a67891c671eab01b07d26fede457571f1e0e1b'
runtimeHead = git(RUNTIME, 'rev-parse', 'HEAD').decode().strip()
runtimeStatus = git(RUNTIME, 'status', '--porcelain=v1', '-z', '--untracked-files=all')
assert runtimeHead == '844389ee069e1fb2e576708842d0b389b4d9a44a' and not runtimeStatus
lock = pin(MAIN / 'shieldd.lock')
assert lock['sha256'] == 'd82d793d0c9e6975ed39044fd40574cdce125792d820399c0fbfdd4f9659fe0c'
result = {'kind': 'READ_ONLY_PRESERVATION_IDENTITY_CHECKPOINT', 'baseline': pin(baseline),
    'protected_files': len(d['protected']), 'foreign_files': len(d['foreign']), 'all_preserved': True,
    'main_head': mainHead, 'main_raw_status': {'bytes': len(mainStatus), 'sha256': hashlib.sha256(mainStatus).hexdigest()},
    'runtime_head': runtimeHead, 'runtime_clean': not runtimeStatus, 'lock': lock,
    'recipe': pin(Path(__file__)), 'scope': 'Exact file and Git identities only. No new proof, semantic correspondence, runtime testing, negative control, atomic evidence refresh or full Transfer certification.'}
(ROOT / 'preservation.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps(result))
