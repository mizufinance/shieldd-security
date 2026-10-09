from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-torsion-point-transport-generated-20261009-01.py').read_text()
for old, new in [
    ('torsion-point-transport-20261009-01', 'torsion-point-transport-20261009-02'),
    ('torsion-point-transport-closure-20261009-01', 'torsion-point-transport-closure-20261009-02'),
    ('torsion-point-transport-closure-inspection-20261009-01', 'torsion-point-transport-closure-inspection-20261009-02'),
    ('torsion-point-transport-cache-20261009-01', 'torsion-point-transport-cache-20261009-02'),
    ('torsion-point-transport-boundary-2026100901', 'torsion-point-transport-boundary-2026100902'),
    ('TransferOwnedTorsionPointTransportBoundary2026100901', 'TransferOwnedTorsionPointTransportBoundary2026100902'),
]:
    body = body.replace(old, new)
target = local / 'prepare-torsion-point-transport-generated-20261009-02.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
