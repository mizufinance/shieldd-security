"""Untrusted arithmetic proposals for the distinct pinned SDK base; zero proof credit."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
R = 6554484396890773809930967563523245729705921265872317281365359162392183254199
D = 19257038036680949359750312669786877991949435402254120286184196891950884077233
SOURCE = DIAG / 'transfer-sdk-source-binding-20261010-01/sources/reddsa-0.5.2/src/constants.rs'
def pin(p):
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
match = re.search(r'pub const SPENDAUTHSIG_BASEPOINT_BYTES: \[u8; 32\] = \[([^]]+)\]', SOURCE.read_text())
assert match
encoded = [int(x) for x in re.findall(r'\d+', match.group(1))]
assert len(encoded) == 32 and all(0 <= x < 256 for x in encoded)
masked = list(encoded); sign = masked[31] >> 7; masked[31] &= 127
y = int.from_bytes(bytes(masked), 'little'); assert y < P
square = (y*y-1) * pow(1+D*y*y, -1, P) % P
def sqrt_mod(value):
    assert pow(value, (P-1)//2, P) == 1
    odd = P-1; count = 0
    while odd % 2 == 0: odd //= 2; count += 1
    nonSquare = 2
    while pow(nonSquare, (P-1)//2, P) != P-1: nonSquare += 1
    c = pow(nonSquare, odd, P); root = pow(value, (odd+1)//2, P); residue = pow(value, odd, P)
    while residue != 1:
        i = 1; squareResidue = residue*residue % P
        while squareResidue != 1: squareResidue = squareResidue*squareResidue % P; i += 1
        factor = pow(c, 2**(count-i-1), P)
        root = root*factor % P; c = factor*factor % P; residue = residue*c % P; count = i
    return root
x = sqrt_mod(square)
if x % 2 != sign: x = P-x
G = (x,y)
def valid(point):
    u,v = point
    return (v*v-u*u-1-D*u*u*v*v) % P == 0
def add(left,right):
    u,v = left; a,b = right; delta = D*u*a*v*b
    return ((u*b+v*a)*pow(1+delta,-1,P)%P, (v*b+u*a)*pow(1-delta,-1,P)%P)
def multiply(point,scalar):
    result = (0,1)
    while scalar:
        if scalar % 2: result = add(result,point)
        point = add(point,point); scalar //= 2
    return result
assert valid(G)
Q = multiply(G,pow(8,-1,R))
points = [Q]
for _ in range(3): points.append(add(points[-1],points[-1]))
assert points[-1] == G and all(valid(point) for point in points)
certificates = []
for index,(u,v) in enumerate(points):
    left = v*v-u*u; right = 1+D*u*u*v*v
    assert (left-right) % P == 0
    certificates.append({'kind':'curve','index':index,'left':left,'right':right,'multiple':(left-right)//P})
for index,((u,v),(outX,outY)) in enumerate(zip(points,points[1:])):
    for axis,left,right in [('x',outX*(1+D*u*u*v*v),u*v+v*u),('y',outY*(1-D*u*u*v*v),v*v+u*u)]:
        assert (left-right) % P == 0
        certificates.append({'kind':'double-row','index':index,'axis':axis,'left':left,'right':right,'multiple':(left-right)//P})
traceX = 39680211447325986415026918192437531897852916166128269978655486138252525496083
traceY = 43044799768094727361329244498846272665229388789665544224645223436242971151146
trace = (-40964*traceX*pow(traceY,-1,P)%P,(traceX+40964)*pow(traceX-40964,-1,P)%P)
traceBytes = bytearray(trace[1].to_bytes(32,'little')); traceBytes[31] |= (trace[0]%2)<<7
result = {'kind':'UNTRUSTED_SDK_SPEND_AUTH_ARITHMETIC_PROPOSALS','recipe':pin(Path(__file__)),
    'sdk_constant_source':pin(SOURCE),'p':P,'r':R,'d':D,'sdk_bytes':encoded,'masked_y_bytes':masked,
    'sign':sign,'sdk_point':G,'eight_preimage':Q,'double_chain':points,'integer_certificates':certificates,
    'retained_traced_edwards_coordinates_proposal':trace,'retained_traced_compressed_bytes_proposal':list(traceBytes),
    'same_base_proposal':list(traceBytes)==encoded,
    'scope':'Arithmetic proposals only. Kernel validation is required. Native source/code/bytes correspondence and full Transfer remain open.',
    'proof_credit':0,'runtime_test_credit':0,'bounded_model_check_credit':0,'semantic_negative_control_credit':0,'certification':False}
target = ROOT / 'proposals.json'; assert not target.exists()
target.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'proposals':pin(target),'sdk_point':G,'eight_preimage':Q,'certificates':len(certificates),
    'same_base_proposal':result['same_base_proposal'],'proof_credit':0,'certification':False}))
