"""Generate finite integer certificates, checked in Lean's kernel, for three actual torsion points.

The integer calculations only choose certificates. Proof credit requires the
separate bounded Lean run; no runtime or semantic-negative-control credit.
"""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
DATA = DIAG / 'transfer-torsion-cardinality49-20261010-01/inputs/candidates49-DATA.json'
data = json.loads(DATA.read_text())
p = data['p']; A = 40962; B = -40964
points = [data['points'][i]['weierstrass'] for i in range(3)]
assert points[0][0] == data['points'][0]['weierstrass'][0]
source = '''import ShielddSecurity.ConcretePointCoordinateRows01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteEightTorsionData01
open TorsionCertifiedField01 ConcretePointTorsion01 ConcretePointCoordinateRows01

'''
defs = []
for i, (x, y) in enumerate(points, 1):
    source += f'def X{i} : F := {x}\ndef Y{i} : F := {y}\n'
    defs += [f'X{i}', f'Y{i}']
s1 = (3 * points[0][0]**2 + 2*A*B*points[0][0] + B*B) * pow(2*points[0][1], -1, p) % p
s2 = (3 * points[1][0]**2 + 2*A*B*points[1][0] + B*B) * pow(2*points[1][1], -1, p) % p
s3 = (points[0][1] - points[1][1]) * pow(points[0][0] - points[1][0], -1, p) % p
for i, slope in enumerate([s1, s2, s3], 1):
    source += f'def S{i} : F := {slope}\n'
    defs.append(f'S{i}')
casts = ', '.join(['Int.cast_add', 'Int.cast_mul', 'Int.cast_pow', 'Int.cast_sub',
    'Int.cast_neg', 'Int.cast_ofNat', 'Int.cast_natCast', 'Int.cast_zero', 'Int.cast_one', 'A', 'B'] + defs)
names = []
def integer(n):
    return f'({n} : Int)'
def certificate(name, goal, lhs, rhs, left_value, right_value, prefix='', suffix=''):
    global source
    assert (left_value - right_value) % p == 0, name
    multiple = (left_value - right_value) // p
    source += f'''\ntheorem {name} : {goal} := by
{prefix}  have integer : {lhs} = {rhs} + {integer(multiple)} * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  {suffix}simpa only [{casts}] using equal
'''
    names.append(name)
def nonzero(name, goal, expr, value, suffix=''):
    global source
    inverse = pow(value, -1, p)
    multiple = (value * inverse - 1) // p
    source += f'''\ntheorem {name} : {goal} := by
  have integer : ({expr}) * {integer(inverse)} = 1 + {integer(multiple)} * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_nonzero _ _ _ integer
  {suffix}simpa only [{casts}] using equal
'''
    names.append(name)
for i, (x,y) in enumerate(points, 1):
    rhs = x*x*x + A*B*x*x + B*B*x
    certificate(f'equation{i}', f'curve.Equation X{i} Y{i}',
        f'{integer(y)} * {integer(y)}',
        f'{integer(x)} * {integer(x)} * {integer(x)} + ({integer(A)} * {integer(B)}) * {integer(x)} * {integer(x)} + ({integer(B)} * {integer(B)}) * {integer(x)}',
        y*y, rhs, prefix=f'  apply (equation_iff X{i} Y{i}).mpr\n  unfold right\n')
for i, slope, target in [(1,s1,points[1]), (2,s2,[0,0])]:
    x,y = points[i-1]; outx,outy=target
    outX,outY = (f'X2',f'Y2') if i==1 else ('0','0')
    nonzero(f'double{i}_nonzero', f'(2 : F) * Y{i} ≠ 0', f'(2 : Int) * {integer(y)}', 2*y)
    certificate(f'double{i}_slope', f'S{i} * (2 * Y{i}) = 3 * X{i} ^ 2 + 2 * (A * B) * X{i} + B * B',
        f'{integer(slope)} * ((2 : Int) * {integer(y)})',
        f'(3 : Int) * {integer(x)} ^ 2 + (2 : Int) * ({integer(A)} * {integer(B)}) * {integer(x)} + {integer(B)} * {integer(B)}',
        slope*2*y, 3*x*x+2*A*B*x+B*B)
    certificate(f'double{i}_x', f'({outX} : F) = S{i} ^ 2 - A * B - X{i} - X{i}',
        integer(outx), f'{integer(slope)} ^ 2 - {integer(A)} * {integer(B)} - {integer(x)} - {integer(x)}',
        outx, slope*slope-A*B-2*x)
    certificate(f'double{i}_y', f'({outY} : F) = S{i} * (X{i} - {outX}) - Y{i}',
        integer(outy), f'{integer(slope)} * ({integer(x)} - {integer(outx)}) - {integer(y)}',
        outy, slope*(x-outx)-y)
x1,y1=points[0]; x2,y2=points[1]; x3,y3=points[2]
nonzero('add13_different', 'X1 ≠ X2', f'{integer(x1)} - {integer(x2)}', x1-x2,
    suffix='apply sub_ne_zero.mp\n  ')
certificate('add13_slope', 'S3 * (X1 - X2) = Y1 - Y2',
    f'{integer(s3)} * ({integer(x1)} - {integer(x2)})', f'{integer(y1)} - {integer(y2)}',
    s3*(x1-x2), y1-y2)
certificate('add13_x', 'X3 = S3 ^ 2 - A * B - X1 - X2',
    integer(x3), f'{integer(s3)} ^ 2 - {integer(A)} * {integer(B)} - {integer(x1)} - {integer(x2)}',
    x3, s3*s3-A*B-x1-x2)
certificate('add13_y', 'Y3 = S3 * (X1 - X3) - Y1',
    integer(y3), f'{integer(s3)} * ({integer(x1)} - {integer(x3)}) - {integer(y1)}',
    y3, s3*(x1-x3)-y1)
source += '\nend ShielddSecurity.ConcreteEightTorsionData01\n'
for name in names:
    q = 'ShielddSecurity.ConcreteEightTorsionData01.' + name
    source += f'\nset_option pp.all true in\n#check @{q}\n#print axioms {q}\n'
dest = ROOT / 'generated/ConcreteEightTorsionData01.lean'
dest.parent.mkdir(exist_ok=False)
dest.write_text(source, encoding='utf-8', newline='\n')
def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
(ROOT / 'generation-review.json').write_text(json.dumps({'generator': pin(Path(__file__)),
    'input': pin(DATA), 'source': pin(dest), 'audits': len(names), 'kernel_credit': 0,
    'runtime_credit': 0, 'semantic_negative_controls': 0}, indent=2) + '\n')
print(json.dumps({'source': pin(dest), 'audits': len(names), 'kernel_credit': 0}))
