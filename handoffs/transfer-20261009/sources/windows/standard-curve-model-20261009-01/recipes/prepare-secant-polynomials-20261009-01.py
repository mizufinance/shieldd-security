from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
body = (local / 'prepare-torsion-algebra-20261009-03.py').read_text()
for old, new in [
    ('torsion-algebra-20261009-03', 'secant-polynomials-20261009-01'),
    ('torsion-algebra-closure-20261009-03', 'secant-polynomials-closure-20261009-01'),
    ('torsion-algebra-closure-inspection-20261009-03', 'secant-polynomials-closure-inspection-20261009-01'),
    ('torsion-algebra-cache-20261009-03', 'secant-polynomials-cache-20261009-01'),
    ('torsion-algebra-boundary-2026100903', 'secant-polynomials-boundary-2026100901'),
    ('TransferOwnedTorsionAlgebraBoundary2026100903', 'TransferOwnedSecantPolynomialsBoundary2026100901'),
    ('EdwardsTorsionAlgebra01', 'EdwardsSecantPolynomials01'),
]:
    body = body.replace(old, new)
start = body.index("scope='")
end = body.index('\nbody=re.sub', start)
body = body[:start] + "scope='Three symbolic secant polynomial identities derived from two Edwards input curve equations, proposed by a coefficient generator and independently checked by Lean. Rational denominator discharge and actual Point secant transport UNPROVED; tangent transport, StandardCurveModel, order, cardinality, native codec, and full Transfer OPEN.'" + body[end:]
target = local / 'prepare-secant-polynomials-generated-20261009-01.py'
assert not target.exists()
target.write_text(body)
exec(compile(body, str(target), 'exec'), {'__file__': str(target), '__name__': '__main__'})
