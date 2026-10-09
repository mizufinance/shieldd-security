from pathlib import Path

local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-windows-connected-subgroup-semantics-20261009-01.py').read_text()
body = body.replace('windows-connected-subgroup-semantics-20261009-01', 'windows-connected-subgroup-semantics-20261009-02')
body = body.replace('handoffs/transfer-20261009/sources/mac/mac-connected-subgroup01/final01/project/ShielddSecurity', 'circuits/ShielddSecurity')
body = body.replace("'TransferFirstSubgroupTables02'], name", "'TransferFirstSubgroupTables02', 'CompilerIndexCoverage01'], name")
body = body.replace("'proof_bytes_changed': False", "'proof_bytes_changed': True, 'parent_commit': 'd7d44ca82712a35a3e40d68af7ae89b25b128ce6'")
previous = next(line for line in body.splitlines() if line.startswith('scope = '))
body = body.replace(previous, "scope = 'Concrete first registry dk against canonical coverage02: all71 original rows imply on-curve preimage and eightfold image; an explicit GLOBAL full-group order premise plus StandardCurveModel/NoUnitSquare/imaginary yields an r-annihilated representation of the claimed key. Native original-row completion preserves all22735 constructed input values and remaining inputs outside11..17. Identity permitted. Concrete deployed curve/codec/group-order/SDK admission and remaining full Transfer graph/state joins remain OPEN.'")
(local / 'prepare-windows-connected-subgroup-semantics-20261009-02.py').write_bytes(body.encode())
