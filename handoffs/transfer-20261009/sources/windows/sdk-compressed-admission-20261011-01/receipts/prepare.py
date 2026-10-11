"""Fresh read-only checkpoint for the final qualified encoding/admission packet."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
target = ROOT / 'preservation_check.py'
assert not target.exists()
target.write_bytes((ROOT.parent / 'transfer-sdk-compressed-admission-checkpoint-20261010-01/preservation_check.py').read_bytes())
print('Exact read-only preservation recipe copied into final fresh checkpoint.')
