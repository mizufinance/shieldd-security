from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-addition-pilot-20261009-06.py').read_text()
for old, new in [
    ('windows-addition-pilot-20261009-06', 'windows-addition-helpers-20261009-01'),
    ('addition-pilot-closure-inspection-20261009-06', 'addition-helpers-closure-inspection-20261009-01'),
    ('inspect-addition-pilot-closure-20261009-06', 'inspect-addition-helpers-closure-20261009-01'),
    ('compose-addition-pilot-cache-20261009-06', 'compose-addition-helpers-cache-20261009-01'),
    ('prepare-addition-pilot-20261009-06', 'prepare-addition-helpers-generated-20261009-01'),
    ('safe-addition-pilot-boundary-2026100906', 'safe-addition-helpers-boundary-2026100901'),
    ('TransferOwnedAdditionPilotBoundary2026100906', 'TransferOwnedAdditionHelpersBoundary2026100901'),
    ('ConcretePointAdditionPilot01', 'ConcretePointCoordinates01'),
]:
    body = body.replace(old, new)
body = body.replace("inspector=inspector.replace('out.write_bytes'", "inspector=inspector.replace(\"for name in ['ShielddSecurity.ConcretePointCoordinates01']:\", \"for name in ['ShielddSecurity.ConcretePointCoordinates01', 'ShielddSecurity.EdwardsExceptionalClassification01']:\")\ninspector=inspector.replace('out.write_bytes'")
body = body.replace("body=body.replace(\"visit('ConcreteEdwardsParameters01')\",\"visit('ConcretePointCoordinates01')\")", "body=body.replace(\"visit('ConcreteEdwardsParameters01')\",\"visit('ConcretePointCoordinates01')\\nvisit('EdwardsExceptionalClassification01')\")")
body = body.replace("for namespace in ['windows-concrete-point-20261009-05'", "for namespace in ['windows-addition-pilot-20261009-06','windows-torsion-algebra-20261009-03','windows-concrete-point-20261009-05'")
start = body.index("scope='")
end = body.index("\nbody=re.sub", start)
body = body[:start] + "scope='Concrete coordinate representation covers all Edwards solutions, is injective, and respects identity and negation; generic cross-zero exceptional classification. No full addition homomorphism, StandardCurveModel, order, cardinality, native codec, or full Transfer credit.'" + body[end:]
target = local / 'prepare-addition-helpers-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
