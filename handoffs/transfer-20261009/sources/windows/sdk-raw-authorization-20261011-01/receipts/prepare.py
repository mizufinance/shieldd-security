"""Read-only final raw endpoint checkpoint, preserving exact reviewed recipe."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
target = ROOT / 'preservation_check.py'
assert not target.exists()
target.write_bytes((ROOT.parent / 'transfer-sdk-compressed-admission-checkpoint-20261010-02/preservation_check.py').read_bytes())
print('Exact read-only136-file preservation/runtime/lock checkpoint recipe prepared.')
