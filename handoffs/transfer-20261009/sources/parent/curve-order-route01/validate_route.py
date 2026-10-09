"""Independent integer checks for a proposed route, never a kernel proof."""
import json,pathlib,math
r=pathlib.Path(__file__).parent;w=json.loads((r/'integer-window.json').read_text());c=json.loads((r/'weierstrass-route-data.json').read_text());p=int(w['p']);order=int(w['r']);s=math.isqrt(p);radius=2*(s+1)
def check(b):
 if not b:raise ValueError('route data mismatch')
check(int(w['floor_sqrt_p'])==s and s*s<=p<(s+1)**2)
check(int(w['strict_hasse_radius_upper'])==radius)
lo=p+1-radius;hi=p+1+radius
check(int(w['lower_inclusive'])==lo and int(w['upper_inclusive'])==hi)
check(7*order<lo<=8*order<=hi<9*order)
check(int(w['trace_p_plus_one_minus_8r'])==p+1-8*order)
check((p+1-8*order)**2<=4*p)
A=c['montgomery']['A'];B=c['montgomery']['B'];d=int(c['d']);a=c['a'];W=c['weierstrass']
check(p==int(c['p']) and a==-1 and A==40962 and B==-40964)
check(((a-d)*A-2*(a+d))%p==0 and ((a-d)*B-4)%p==0)
check((W['a1'],W['a2'],W['a3'],W['a4'],W['a6'])==(0,A*B,0,B*B,0))
# Standard b-invariants for the displayed long Weierstrass coefficients.
b2=4*W['a2'];b4=2*W['a4'];b6=0;b8=-(W['a4']**2)
delta=-(b2*b2)*b8-8*(b4**3)-27*b6*b6+9*b2*b4*b6
check(delta==int(W['discriminant_integer'])==16*(B**6)*(A*A-4))
check(0<delta<p)
print(json.dumps({'status':'passed','integer_window':True,'montgomery_parameter_equations':True,'weierstrass_discriminant':True,'kernel_run':False,'proof_credit':0}))
