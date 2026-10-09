from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
prior = diag / 'windows-secant-polynomials-20261009-01-kernel'
assert (prior / 'complete.txt').exists() and (prior / 'exit.txt').read_text().strip() == '0'
body = (local / 'prepare-secant-polynomials-generated-20261009-01.py').read_text()
for old, new in [
    ('secant-polynomials-20261009-01', 'secant-rational-20261009-01'),
    ('secant-polynomials-closure-20261009-01', 'secant-rational-closure-20261009-01'),
    ('secant-polynomials-closure-inspection-20261009-01', 'secant-rational-closure-inspection-20261009-01'),
    ('secant-polynomials-cache-20261009-01', 'secant-rational-cache-20261009-01'),
    ('secant-polynomials-boundary-2026100901', 'secant-rational-boundary-2026100901'),
    ('TransferOwnedSecantPolynomialsBoundary2026100901', 'TransferOwnedSecantRationalBoundary2026100901'),
    ('EdwardsSecantPolynomials01', 'EdwardsSecantRational01'),
]:
    body = body.replace(old, new)
body = body.replace('for namespace in [', "for namespace in ['windows-secant-polynomials-20261009-01',")
start = body.index("scope='")
end = body.index('\nbody=re.sub', start)
body = body[:start] + "scope='Generic quotient discharge lemmas and secant slope row. Conditional normalized coordinate rows explicitly require the checked polynomial identities and nonzero denominators. Actual Edwards-to-Point regular secant transport, tangent transport, StandardCurveModel, order, cardinality, native codec, and full Transfer OPEN.'" + body[end:]
target = local / 'prepare-secant-rational-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
