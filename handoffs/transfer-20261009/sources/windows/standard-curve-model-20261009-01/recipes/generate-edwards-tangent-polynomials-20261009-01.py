from pathlib import Path
import hashlib,json,os,sys
sys.path.insert(0,'C:/src/shieldd-transfer-handoffs/symbolic-exploration-deps01')
import sympy as s
assert s.__version__ == '1.14.0'
local=Path('C:/src/shieldd-transfer-handoffs')
target=Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity/EdwardsTangentPolynomials01.lean')
assert not target.exists()
x,y,d=s.symbols('x y d')
delta,diagonal,cross=d*x*x*y*y,y*y+x*x,2*x*y
m,p=1-delta-diagonal,1-delta+diagonal
k,h=2+y-d*x*x*y,2*x
curve=y*y-x*x-1-d*x*x*y*y
polynomials={
 'tangent_slope_polynomial':s.expand(4*k*(1-y*y)+x*x*((1+d)*(3*(1+y)**2+(1-y)**2)+4*(1-d)*(1-y*y))),
 'tangent_x_polynomial':s.expand(((1+d)*(p*(1-y)+2*(1+y)*m)+2*(1-d)*m*(1-y))*h*h+4*k*k*m*(1-y)),
 'tangent_y_polynomial':s.expand((1+delta)*p*h*(1-y)*x-k*((1+y)*m-p*(1-y))*cross*x+(1+y)*m*cross*h),
}
basis=s.groebner([curve],d,x,y)
assert s.expand(basis.polys[0].as_expr()+curve)==0
def lean(e):
 if e.is_Symbol:return str(e)
 if e.is_Integer:return str(e) if e>=0 else '('+str(e)+')'
 if e.is_Add:return '('+' + '.join(map(lean,e.args))+')'
 if e.is_Mul:return '('+' * '.join(map(lean,e.args))+')'
 if e.is_Pow:
  assert e.exp.is_Integer and e.exp>=0
  return '('+lean(e.base)+' ^ '+str(e.exp)+')'
 raise TypeError(e)
body='''import ShielddSecurity.EdwardsWeierstrassEquiv01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsTangentPolynomials01
variable {F : Type} [Field F]

'''
definitions='''    let delta := d * x * x * y * y
    let diagonal := y * y + x * x
    let cross := 2 * x * y
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let k := 2 + y - d * x * x * y
    let h := 2 * x
'''
statements={
 'tangent_slope_polynomial':'4 * k * (1 - y * y) + x ^ 2 *\n      ((1 + d) * (3 * (1 + y) ^ 2 + (1 - y) ^ 2) +\n        4 * (1 - d) * (1 - y * y)) = 0',
 'tangent_x_polynomial':'((1 + d) * (p * (1 - y) + 2 * (1 + y) * m) +\n      2 * (1 - d) * m * (1 - y)) * h ^ 2 + 4 * k ^ 2 * m * (1 - y) = 0',
 'tangent_y_polynomial':'(1 + delta) * p * h * (1 - y) * x -\n      k * ((1 + y) * m - p * (1 - y)) * cross * x +\n      (1 + y) * m * cross * h = 0',
}
derivations={}
for name,e in polynomials.items():
 qs,r=basis.reduce(e)
 assert r==0 and s.expand(e-qs[0]*basis.polys[0].as_expr())==0
 q=s.factor(qs[0])
 body+=f'theorem {name} (d x y : F)\n    (input : y * y - x * x = 1 + d * x * x * y * y) :\n'
 body+=definitions+'    '+statements[name]+' := by\n  dsimp only\n'
 body+=f'  linear_combination -{lean(q)} * input\n\n'
 derivations[name]={'polynomial_terms':len(s.Poly(e,d,x,y).terms()),'coefficient_terms':len(s.Poly(q,d,x,y).terms()),'kernel_status':'UNRUN; no proof credit'}
body+='end ShielddSecurity.EdwardsTangentPolynomials01\n'
pending=target.with_suffix('.lean.pending-20261009-01')
assert not pending.exists()
pending.write_bytes(body.encode());os.replace(pending,target)
record=local/'edwards-tangent-polynomial-generation-20261009-01.json'
assert not record.exists()
record.write_text(json.dumps({'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'sympy_version':s.__version__,
 'derivations':derivations,'proof_credit':0,'full_transfer':'OPEN'},indent=2)+'\n')
print(record.read_text())
