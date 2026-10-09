"""Generate candidate affine Weierstrass scalar data; no kernel/group/order credit."""
import argparse, hashlib, json
from pathlib import Path
EXPECTED = 'cc8334c14d8d20d88c93d04e5f7c349d575949d3be13b1c3579355900b092d0a'

def make(path):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED:
        raise ValueError('Edwards candidate identity mismatch')
    e = json.loads(raw); p = e['p']; A = 40962; B = -40964 % p
    a2 = A * B % p; a4 = B * B % p
    def mapped(point):
        x, y = point
        if point == [0, 1]: return None
        if point == [0, p-1]: return [0, 0]
        t = (1+y) * pow((1-y)%p, -1, p) % p
        return [B*t%p, B*B*t*pow(x,-1,p)%p]
    def op(left, right):
        if left is None: return {'case':'left_infinity', 'after':right}
        if right is None: return {'case':'right_infinity', 'after':left}
        x,y = left; u,v = right
        if x == u and (y+v)%p == 0:
            return {'case':'inverse', 'after':None}
        if left == right:
            kind = 'double'; numerator = (3*x*x+2*a2*x+a4)%p; denominator = 2*y%p
        else:
            kind = 'add'; numerator = (v-y)%p; denominator = (u-x)%p
        inverse = pow(denominator, -1, p); slope = numerator*inverse%p
        X = (slope*slope-a2-x-u)%p; Y = (slope*(x-X)-y)%p
        return {'case':kind, 'denominator_inverse':inverse, 'slope':slope, 'after':[X,Y]}
    base = mapped(e['base']); point = None; steps = []
    for entry in e['steps']:
        doubling = op(point,point)
        if doubling['after'] != mapped(entry['doubled']): raise ValueError('doubling map mismatch')
        addition = op(doubling['after'],base) if entry['bit'] else None
        point = addition['after'] if addition else doubling['after']
        if point != mapped(entry['after']): raise ValueError('addition map mismatch')
        steps.append({'bit':entry['bit'],'prefix':entry['prefix'],'doubling':doubling,'addition':addition,'after':point})
    return {'schema':'weierstrass-point-order-candidate-v1','runtime_sha':e['runtime_sha'],
        'edwards_candidate_sha256':EXPECTED,'p':p,'r':e['r'],'A':A,'B':B,'a2':a2,'a4':a4,
        'base':base,'steps':steps,'proof_credit':0,
        'scope':'Candidate arithmetic trace on Y^2=X^3+a2*X^2+a4*X. No primality of r, Mathlib group law, kernel point order or full curve cardinality credit.'}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--edwards',type=Path,required=True); parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    with args.output.open('x') as f: json.dump(make(args.edwards),f,indent=2); f.write('\n')
