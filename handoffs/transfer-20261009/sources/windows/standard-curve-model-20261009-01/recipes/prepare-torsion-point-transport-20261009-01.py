from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
origin = diag / 'windows-origin-addition-20261009-01-kernel'
assert (origin / 'complete.txt').exists() and (origin / 'exit.txt').read_text().strip() == '0'
body = (local / 'prepare-origin-addition-generated-20261009-01.py').read_text()
for old, new in [
    ('windows-origin-addition-20261009-01', 'windows-torsion-point-transport-20261009-01'),
    ('origin-addition-closure-20261009-01', 'torsion-point-transport-closure-20261009-01'),
    ('origin-addition-closure-inspection-20261009-01', 'torsion-point-transport-closure-inspection-20261009-01'),
    ('origin-addition-cache-20261009-01', 'torsion-point-transport-cache-20261009-01'),
    ('prepare-origin-addition-generated-20261009-01', 'prepare-torsion-point-transport-generated-20261009-01'),
    ('origin-addition-boundary-2026100901', 'torsion-point-transport-boundary-2026100901'),
    ('TransferOwnedOriginAdditionBoundary2026100901', 'TransferOwnedTorsionPointTransportBoundary2026100901'),
    ('ConcreteOriginAdditionPilot01', 'ConcreteTorsionAddition01'),
]:
    body = body.replace(old, new)
body = body.replace("for namespace in ['windows-point-operation-rows-20261009-03'", "for namespace in ['windows-origin-addition-20261009-01','windows-addition-pilot-20261009-06','windows-point-operation-rows-20261009-03'")
start = body.index("scope='")
end = body.index("\nbody=re.sub", start)
body = body[:start] + "scope='Concrete Edwards torsion addition transport to actual Mathlib Point, including identity, torsion, and every regular point. General secant/tangent addition homomorphism, StandardCurveModel, order, cardinality, native codec, and full Transfer remain OPEN.'" + body[end:]
target = local / 'prepare-torsion-point-transport-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
