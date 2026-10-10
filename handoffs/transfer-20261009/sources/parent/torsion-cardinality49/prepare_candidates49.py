"""Portable integer DATA candidate, no Lean/native/certification claims.

Eight independent point constants; source origin is recorded only as provenance.
Output always writes an exclusive new JSON file. No imports beyond stdlib,
compiler calls, downloads, subprocesses, caches or imported historical helpers.
"""
import argparse
import json

P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
R = 6554484396890773809930967563523245729705921265872317281365359162392183254199
D = -10240 * pow(10241, -1, P) % P
A, B = 40962, -40964
POINTS = [(51487464086487745867707624970564403863932192230710361188278096157071779040579, 33175629719884006543435607313513638533300198751199617432860030069151083304669), (52435875175126190475982595682112313518914282969839895044333406231173219221505, 0), (51487464086487745867707624970564403863932192230710361188278096157071779040579, 19260245455242183936012133194672327304390353749328020389743628630787497879844), (0, 52435875175126190479447740508185965837690552500527637822603658699938581184512), (948411088638444611740115537621561973758360269817276634325562542866802143934, 19260245455242183936012133194672327304390353749328020389743628630787497879844), (3465144826073652318776269530687742778270252468765361963008, 0), (948411088638444611740115537621561973758360269817276634325562542866802143934, 33175629719884006543435607313513638533300198751199617432860030069151083304669), (0, 1)]

def add(left, right):
    x,y = left; u,v = right
    k = D*x*u*y*v % P
    return ((x*v+y*u)*pow(1+k,-1,P)%P,
            (y*v+x*u)*pow(1-k,-1,P)%P)

def validate():
    result=[]
    if len(POINTS)!=8 or len(set(POINTS))!=8:
        raise ValueError('eight distinct constants required')
    for i,point in enumerate(POINTS):
        x,y=point
        if not (0<=x<P and 0<=y<P and (y*y-x*x-1-D*x*x*y*y)%P==0):
            raise ValueError('noncanonical or off-curve candidate')
        trace=[point]; current=point; order=1
        while current!=(0,1) and order<16:
            current=add(current,point);trace.append(current);order+=1
        if current!=(0,1) or order not in (1,2,4,8):
            raise ValueError('unexpected finite point order')
        if y==1:
            if point!=(0,1):raise ValueError('unexpected identity fibre')
            mapped=None; euler=None
        elif x==0:
            if y!=P-1:raise ValueError('unexpected torsion fibre')
            mapped=(0,0);euler=0
        else:
            u=(1+y)*pow(1-y,-1,P)%P
            v=u*pow(x,-1,P)%P
            mapped=(B*u%P,B*B*v%P)
            X,Y=mapped
            if (Y*Y-X*X*X-A*B*X*X-B*B*X)%P:
                raise ValueError('mapped Weierstrass equation')
            euler=pow(X,(P-1)//2,P)
        if order==8 and euler!=P-1:
            raise ValueError('order-eight X is not a nonresidue candidate')
        result.append({'index':i,'edwards':point,'integer_addition_trace':trace,
                       'observed_order':order,'weierstrass':mapped,'X_euler':euler})
    generator=POINTS[0]; current=(0,1); multiples=[]
    for _ in range(8):
        multiples.append(current);current=add(current,generator)
    if current!=(0,1) or set(multiples)!=set(POINTS):
        raise ValueError('cyclic eight-point list mismatch')
    discriminant_euler=pow((A*A-4)%P,(P-1)//2,P)
    if discriminant_euler!=P-1 or not (2*P+1<24*R):
        raise ValueError('candidate discriminant/elementary upper window')
    return {'kind':'INTEGER_DATA_ONLY_NOT_KERNEL_PROOF',
            'p':P,'r':R,'d':D,'A':A,'B':B,'points':result,
            'generator_index':0,'cyclic_multiples':multiples,
            'A_squared_minus_four_euler':discriminant_euler,
            'upper_window':{'2p_plus1':2*P+1,'24r':24*R,'strict':True},
            'scope':'Finite integer candidates only. No global point count, imported model, native agreement or complete Transfer theorem is proved.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    with open(args.output,'x',encoding='utf-8') as stream:
        json.dump(validate(),stream,indent=2);stream.write('\n')
