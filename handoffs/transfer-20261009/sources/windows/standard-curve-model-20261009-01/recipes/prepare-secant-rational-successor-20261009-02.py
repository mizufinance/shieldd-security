from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-secant-rational-generated-20261009-01.py').read_text()
old = '"for namespace in [\'windows-secant-polynomials-20261009-01\',",'
assert body.count(old) == 1
body = body.replace(old, '"for namespace in [",', 1)
for old, new in [
    ('secant-rational-20261009-01', 'secant-rational-20261009-02'),
    ('secant-rational-closure-20261009-01', 'secant-rational-closure-20261009-02'),
    ('secant-rational-closure-inspection-20261009-01', 'secant-rational-closure-inspection-20261009-02'),
    ('secant-rational-cache-20261009-01', 'secant-rational-cache-20261009-02'),
    ('secant-rational-boundary-2026100901', 'secant-rational-boundary-2026100902'),
    ('TransferOwnedSecantRationalBoundary2026100901', 'TransferOwnedSecantRationalBoundary2026100902'),
]:
    body = body.replace(old, new)
target = local / 'prepare-secant-rational-generated-20261009-02.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
