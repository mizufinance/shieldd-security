from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-point-operation-rows-20261009-03.py').read_text()
for old, new in [
    ('windows-point-operation-rows-20261009-03', 'windows-origin-addition-20261009-01'),
    ('point-operation-rows-closure-20261009-03', 'origin-addition-closure-20261009-01'),
    ('point-operation-rows-closure-inspection-20261009-03', 'origin-addition-closure-inspection-20261009-01'),
    ('point-operation-rows-cache-20261009-03', 'origin-addition-cache-20261009-01'),
    ('prepare-point-operation-rows-20261009-03', 'prepare-origin-addition-generated-20261009-01'),
    ('point-operation-rows-boundary-2026100903', 'origin-addition-boundary-2026100901'),
    ('TransferOwnedPointOperationRowsBoundary2026100903', 'TransferOwnedOriginAdditionBoundary2026100901'),
    ('ConcretePointOperationRows01', 'ConcreteOriginAdditionPilot01'),
]:
    body = body.replace(old, new)
body = body.replace("for namespace in ['windows-concrete-point-20261009-05'", "for namespace in ['windows-point-operation-rows-20261009-03','windows-torsion-algebra-20261009-03','windows-concrete-point-20261009-05'")
start = body.index("scope='")
end = body.index("\nbody=re.sub", start)
body = body[:start] + "scope='Concrete actual Mathlib Point origin translation derives reciprocal output coordinates and curve membership; origin doubles to zero. Full Edwards torsion transport, general addition homomorphism, StandardCurveModel, order, cardinality, native codec, and full Transfer remain OPEN.'" + body[end:]
target = local / 'prepare-origin-addition-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
