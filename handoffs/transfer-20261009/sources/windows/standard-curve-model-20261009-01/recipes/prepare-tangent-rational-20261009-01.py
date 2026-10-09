from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-secant-rational-generated-20261009-02.py').read_text()
for old, new in [
    ('secant-rational-20261009-02', 'tangent-rational-20261009-01'),
    ('secant-rational-closure-20261009-02', 'tangent-rational-closure-20261009-01'),
    ('secant-rational-closure-inspection-20261009-02', 'tangent-rational-closure-inspection-20261009-01'),
    ('secant-rational-cache-20261009-02', 'tangent-rational-cache-20261009-01'),
    ('secant-rational-boundary-2026100902', 'tangent-rational-boundary-2026100901'),
    ('TransferOwnedSecantRationalBoundary2026100902', 'TransferOwnedTangentRationalBoundary2026100901'),
    ('EdwardsSecantRational01', 'EdwardsTangentRational01'),
]:
    body = body.replace(old, new)
old = "for namespace in ['windows-secant-polynomials-20261009-01'"
assert body.count(old) == 1
body = body.replace(old, "for namespace in ['windows-secant-rational-20261009-02','windows-secant-polynomials-20261009-01'", 1)
start = body.index("scope='")
end = body.index('\nbody=re.sub', start)
body = body[:start] + "scope='Three symbolic tangent polynomial identities from one Edwards input curve equation, plus exact parameter discharge of the normalized tangent slope. Actual Point tangent transport, all-pairs addition homomorphism, StandardCurveModel, order, cardinality, native codec, and full Transfer OPEN.'" + body[end:]
target = local / 'prepare-tangent-rational-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
