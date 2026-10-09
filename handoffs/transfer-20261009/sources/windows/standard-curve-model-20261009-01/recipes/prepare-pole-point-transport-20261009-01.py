from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
prior = diag / 'windows-torsion-point-transport-20261009-03-kernel'
assert (prior / 'complete.txt').exists() and (prior / 'exit.txt').read_text().strip() == '0'
body = (local / 'prepare-torsion-point-transport-generated-20261009-03.py').read_text()
for old, new in [
    ('torsion-point-transport-20261009-03', 'pole-point-transport-20261009-01'),
    ('torsion-point-transport-closure-20261009-03', 'pole-point-transport-closure-20261009-01'),
    ('torsion-point-transport-closure-inspection-20261009-03', 'pole-point-transport-closure-inspection-20261009-01'),
    ('torsion-point-transport-cache-20261009-03', 'pole-point-transport-cache-20261009-01'),
    ('torsion-point-transport-boundary-2026100903', 'pole-point-transport-boundary-2026100901'),
    ('TransferOwnedTorsionPointTransportBoundary2026100903', 'TransferOwnedPolePointTransportBoundary2026100901'),
    ('ConcreteTorsionAddition01', 'ConcretePoleAddition01'),
]:
    body = body.replace(old, new)
body = body.replace("for namespace in ['windows-origin-addition-20261009-01'", "for namespace in ['windows-torsion-point-transport-20261009-03','windows-addition-helpers-20261009-01','windows-origin-addition-20261009-01'")
start = body.index("scope='")
end = body.index('\nbody=re.sub', start)
body = body[:start] + "scope='Concrete Edwards pole addition transport to actual Mathlib Point: every vanishing x numerator is an inverse or opposite-y pair. General regular secant/tangent addition homomorphism, StandardCurveModel, order, cardinality, native codec, and full Transfer remain OPEN.'" + body[end:]
target = local / 'prepare-pole-point-transport-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
