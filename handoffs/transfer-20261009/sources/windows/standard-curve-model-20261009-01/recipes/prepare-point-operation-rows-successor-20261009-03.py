from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-point-operation-rows-20261009-01.py').read_text()
for old, new in [
    ('point-operation-rows-20261009-01', 'point-operation-rows-20261009-03'),
    ('point-operation-rows-cache-20261009-01', 'point-operation-rows-cache-20261009-03'),
    ('point-operation-rows-closure-20261009-01', 'point-operation-rows-closure-20261009-03'),
    ('point-operation-rows-closure-inspection-20261009-01', 'point-operation-rows-closure-inspection-20261009-03'),
    ('point-operation-rows-boundary-2026100901', 'point-operation-rows-boundary-2026100903'),
    ('TransferOwnedPointOperationRowsBoundary2026100901', 'TransferOwnedPointOperationRowsBoundary2026100903'),
]:
    body = body.replace(old, new)
target = local / 'prepare-point-operation-rows-20261009-03.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
