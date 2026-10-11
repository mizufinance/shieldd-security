"""Copy the exact read-only preservation recipe into a fresh checkpoint."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-sdk-codec-checkpoint-20261010-01/preservation_check.py'
target = ROOT / 'preservation_check.py'
assert not target.exists()
target.write_bytes(prior.read_bytes())
print('Exact read-only preservation recipe copied; no certification credit.')
