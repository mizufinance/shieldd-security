from pathlib import Path
import hashlib
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
fetch=local/'fetch-point-official-artifacts-20261009-02.py'
body=(local/'fetch-point-official-artifacts-20261009-01.py').read_text()
body=body.replace('point-artifact-stage-20261009-01','point-artifact-stage-20261009-02')
body=body.replace('os.setpgid(0,0)', 'if os.getpgrp()!=os.getpid():os.setpgid(0,0)\nassert os.getpgrp()==os.getpid()')
assert not fetch.exists();fetch.write_bytes(body.encode())
cleanup=local/'stop-point-owned-fetch-20261009-02.py'
body=(local/'stop-point-owned-fetch-20261009-01.py').read_text().replace('point-artifact-stage-20261009-01','point-artifact-stage-20261009-02')
assert not cleanup.exists();cleanup.write_bytes(body.encode())
guard=diag/'root-windows-point-cache-20261009-02.ps1'
body=(diag/'root-windows-point-cache-20261009-01.ps1').read_text().replace('windows-point-cache-20261009-01','windows-point-cache-20261009-02')
body=body.replace('fetch-point-official-artifacts-20261009-01','fetch-point-official-artifacts-20261009-02').replace('stop-point-owned-fetch-20261009-01','stop-point-owned-fetch-20261009-02')
body=body.replace('point-artifact-stage-20261009-01','point-artifact-stage-20261009-02')
assert not guard.exists();guard.write_bytes(body.encode())
helper=local/'run-safe-windows-point-cache-20261009-02.ps1'
body=(local/'run-safe-windows-point-cache-20261009-01.ps1').read_text().replace('windows-point-cache-20261009-01','windows-point-cache-20261009-02')
body=body.replace('safe-point-cache-boundary-2026100901','safe-point-cache-boundary-2026100902')
body=body.replace(hashlib.sha256((diag/'root-windows-point-cache-20261009-01.ps1').read_bytes()).hexdigest(),hashlib.sha256(guard.read_bytes()).hexdigest())
assert not helper.exists();helper.write_bytes(body.encode());print(hashlib.sha256(guard.read_bytes()).hexdigest())
