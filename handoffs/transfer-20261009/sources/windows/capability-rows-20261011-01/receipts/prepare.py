"""Prepare the unchanged read-only preservation checkpoint."""
import hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
source=ROOT.parent/'transfer-sdk-raw-authorization-checkpoint-20261010-01/preservation_check.py'
data=source.read_bytes()
assert hashlib.sha256(data).hexdigest()=='a1335795d4ffaf7e3ec797ea044fa424c13ddfcb8b7c117a612a7e221be37e74'
target=ROOT/'preservation_check.py';assert not target.exists();target.write_bytes(data)
print('Exact136-file read-only preservation recipe prepared.')
