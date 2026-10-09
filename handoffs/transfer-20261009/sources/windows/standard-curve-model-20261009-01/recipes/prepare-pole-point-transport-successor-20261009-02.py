from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-pole-point-transport-generated-20261009-01.py').read_text()
for old, new in [
    ('pole-point-transport-20261009-01', 'pole-point-transport-20261009-02'),
    ('pole-point-transport-closure-20261009-01', 'pole-point-transport-closure-20261009-02'),
    ('pole-point-transport-closure-inspection-20261009-01', 'pole-point-transport-closure-inspection-20261009-02'),
    ('pole-point-transport-cache-20261009-01', 'pole-point-transport-cache-20261009-02'),
    ('pole-point-transport-boundary-2026100901', 'pole-point-transport-boundary-2026100902'),
    ('TransferOwnedPolePointTransportBoundary2026100901', 'TransferOwnedPolePointTransportBoundary2026100902'),
]:
    body = body.replace(old, new)
target = local / 'prepare-pole-point-transport-generated-20261009-02.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
