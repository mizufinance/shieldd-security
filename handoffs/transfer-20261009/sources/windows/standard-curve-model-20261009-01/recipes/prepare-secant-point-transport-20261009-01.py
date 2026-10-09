from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
prior = diag / 'windows-secant-rational-20261009-02-kernel'
assert (prior / 'complete.txt').exists() and (prior / 'exit.txt').read_text().strip() == '0'
body = (local / 'prepare-pole-point-transport-generated-20261009-02.py').read_text()
for old, new in [
    ('pole-point-transport-20261009-02', 'secant-point-transport-20261009-01'),
    ('pole-point-transport-closure-20261009-02', 'secant-point-transport-closure-20261009-01'),
    ('pole-point-transport-closure-inspection-20261009-02', 'secant-point-transport-closure-inspection-20261009-01'),
    ('pole-point-transport-cache-20261009-02', 'secant-point-transport-cache-20261009-01'),
    ('pole-point-transport-boundary-2026100902', 'secant-point-transport-boundary-2026100901'),
    ('TransferOwnedPolePointTransportBoundary2026100902', 'TransferOwnedSecantPointTransportBoundary2026100901'),
    ('ConcretePoleAddition01', 'ConcreteSecantAddition01'),
]:
    body = body.replace(old, new)
old = "for namespace in ['windows-torsion-point-transport-20261009-03'"
assert body.count(old) == 1
body = body.replace(old, "for namespace in ['windows-secant-rational-20261009-02','windows-secant-polynomials-20261009-01','windows-pole-point-transport-20261009-02','windows-torsion-point-transport-20261009-03'", 1)
start = body.index("scope='")
end = body.index('\nbody=re.sub', start)
body = body[:start] + "scope='Concrete Edwards addition transport to actual Mathlib Point on regular secants with distinct y coordinates and nonzero cross numerator. Every denominator and coordinate row is derived from the input curve equations and exact parameters. Tangent transport, all-pairs addition homomorphism, StandardCurveModel, order, cardinality, native codec, and full Transfer OPEN.'" + body[end:]
target = local / 'prepare-secant-point-transport-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
