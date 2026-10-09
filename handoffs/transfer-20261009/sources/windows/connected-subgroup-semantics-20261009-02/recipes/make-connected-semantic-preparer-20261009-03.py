from pathlib import Path
local=Path('C:/src/shieldd-transfer-handoffs')
body=(local/'prepare-windows-connected-subgroup-semantics-20261009-02.py').read_text()
body=body.replace('windows-connected-subgroup-semantics-20261009-02','windows-connected-subgroup-semantics-20261009-03')
(local/'prepare-windows-connected-subgroup-semantics-20261009-03.py').write_bytes(body.encode())
