from pathlib import Path
import hashlib, json, os, sys
sys.path.insert(0, 'C:/src/shieldd-transfer-handoffs/symbolic-exploration-deps01')
import sympy as s
assert s.__version__ == '1.14.0'

local = Path('C:/src/shieldd-transfer-handoffs')
target = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity/EdwardsSecantPolynomials01.lean')
assert not target.exists(), 'fresh generated proof source required'
x, z, y, w, d = s.symbols('x z y w d')
delta, diagonal, cross = d*x*z*y*w, y*w+x*z, x*w+y*z
m, p = 1-delta-diagonal, 1-delta+diagonal
n, h = z*(1+y)*(1-w)-x*(1+w)*(1-y), 2*x*z*(y-w)
cl, cr = y*y-x*x-1-d*x*x*y*y, w*w-z*z-1-d*z*z*w*w
ey = s.expand((1+delta)*p*h*(1-y)*x - n*((1+y)*m-p*(1-y))*cross*x + (1+y)*m*cross*h)
ex = s.expand(((1+d)*(p*(1-y)*(1-w)+2*(1-y*w)*m)+2*(1-d)*m*(1-y)*(1-w))*h*h
    +4*n*n*m*(1-y)*(1-w))
basis = s.groebner([cl,cr],d,x,z,y,w)
interaction = z*z*w*w*cl - x*x*y*y*cr
assert len(basis.polys) == 3
assert s.expand(basis.polys[0].as_expr()+cl) == 0
assert s.expand(basis.polys[1].as_expr()+cr) == 0
assert s.expand(basis.polys[2].as_expr()-interaction) == 0

def lean(expression):
    if expression.is_Symbol: return str(expression)
    if expression.is_Integer: return str(expression) if expression >= 0 else '('+str(expression)+')'
    if expression.is_Add: return '('+' + '.join(map(lean,expression.args))+')'
    if expression.is_Mul: return '('+' * '.join(map(lean,expression.args))+')'
    if expression.is_Pow:
        assert expression.exp.is_Integer and expression.exp >= 0
        return '('+lean(expression.base)+' ^ '+str(expression.exp)+')'
    raise TypeError(expression)

header = '''import ShielddSecurity.EdwardsWeierstrassEquiv01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsSecantPolynomials01
variable {F : Type} [Field F]

/-- Generated symbolic certificate from the two input curve equations.
The generator proposes coefficients; Lean checks each polynomial identity. -/
theorem curve_interaction (d x z y w : F)
    (left : y * y - x * x = 1 + d * x * x * y * y)
    (right : w * w - z * z = 1 + d * z * z * w * w) :
    -w ^ 2 * x ^ 2 * y ^ 2 - w ^ 2 * x ^ 2 * z ^ 2 +
      w ^ 2 * y ^ 2 * z ^ 2 - w ^ 2 * z ^ 2 +
      x ^ 2 * y ^ 2 * z ^ 2 + x ^ 2 * y ^ 2 = 0 := by
  linear_combination z ^ 2 * w ^ 2 * left - x ^ 2 * y ^ 2 * right

'''
definitions = '''    let delta := d * x * z * y * w
    let diagonal := y * w + x * z
    let cross := x * w + y * z
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let n := z * (1 + y) * (1 - w) - x * (1 + w) * (1 - y)
    let h := 2 * x * z * (y - w)
'''
statements = {
    'secant_y_polynomial': '(1 + delta) * p * h * (1 - y) * x -\n      n * ((1 + y) * m - p * (1 - y)) * cross * x +\n      (1 + y) * m * cross * h = 0',
    'secant_x_polynomial': '((1 + d) * (p * (1 - y) * (1 - w) + 2 * (1 - y * w) * m) +\n      2 * (1 - d) * m * (1 - y) * (1 - w)) * h ^ 2 +\n      4 * n ^ 2 * m * (1 - y) * (1 - w) = 0',
}
body, derivations = header, {}
for name, expression in [('secant_y_polynomial',ey),('secant_x_polynomial',ex)]:
    coefficients, remainder = basis.reduce(expression)
    assert remainder == 0
    assert s.expand(expression - sum(q*g.as_expr() for q,g in zip(coefficients,basis.polys))) == 0
    q1,q2,q3 = [s.factor(q) for q in coefficients]
    body += f'theorem {name} (d x z y w : F)\n'
    body += '    (left : y * y - x * x = 1 + d * x * x * y * y)\n'
    body += '    (right : w * w - z * z = 1 + d * z * z * w * w) :\n'
    body += definitions + '    ' + statements[name] + ' := by\n'
    body += '  have mixed := curve_interaction d x z y w left right\n'
    body += '  dsimp only\n'
    body += f'  linear_combination -{lean(q1)} * left - {lean(q2)} * right + {lean(q3)} * mixed\n\n'
    derivations[name] = {'polynomial_terms':len(s.Poly(expression,d,x,z,y,w).terms()),
        'coefficient_terms':[len(s.Poly(q,d,x,z,y,w).terms()) for q in coefficients],
        'symbolic_remainder':'0', 'kernel_status':'UNRUN; no proof credit'}
body += 'end ShielddSecurity.EdwardsSecantPolynomials01\n'
pending = target.with_suffix('.lean.pending-20261009-01')
assert not pending.exists()
pending.write_bytes(body.encode())
os.replace(pending,target)
record = local / 'edwards-secant-polynomial-generation-20261009-01.json'
assert not record.exists()
record.write_text(json.dumps({'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'sympy_version':s.__version__,
    'derivations':derivations,'full_transfer':'OPEN','proof_credit':0},indent=2)+'\n')
print(record.read_text())
