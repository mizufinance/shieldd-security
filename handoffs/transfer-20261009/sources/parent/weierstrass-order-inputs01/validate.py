"""Independent multiplication-equation validation of candidate data, not a proof."""
import argparse, copy, hashlib, json, time
from pathlib import Path
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
R = 6554484396890773809930967563523245729705921265872317281365359162392183254199
SOURCE = 'cc8334c14d8d20d88c93d04e5f7c349d575949d3be13b1c3579355900b092d0a'

def require(condition, name):
    if not condition: raise ValueError(name)

def validate(c, e):
    B = -40964 % P; a2 = 40962*B%P; a4 = B*B%P
    require((c['p'],c['r'],c['A'],c['B'],c['a2'],c['a4']) == (P,R,40962,B,a2,a4),'parameters')
    require(c['edwards_candidate_sha256']==SOURCE,'source_identity')
    def scalar(n): require(type(n) is int and 0<=n<P,'canonical_field_element')
    def point(q):
        if q is None: return
        require(type(q) is list and len(q)==2,'point_shape')
        x,y=q; scalar(x);scalar(y)
        require((y*y-x*x*x-a2*x*x-a4*x)%P==0,'curve_equation')
    def mapped(q, source):
        point(q);x,y=source
        if source==[0,1]: require(q is None,'identity_map');return
        if source==[0,P-1]: require(q==[0,0],'torsion_map');return
        require(q is not None and x!=0 and (1-y)%P!=0,'map_domain')
        X,Y=q
        require((X*(1-y)-B*(1+y))%P==0,'map_x')
        require((Y*x*(1-y)-B*B*(1+y))%P==0,'map_y')
    def operation(left,right,op):
        point(left);point(right);point(op['after']);kind=op['case']
        if left is None:
            require(kind=='left_infinity' and op['after']==right,'left_identity');return
        if right is None:
            require(kind=='right_infinity' and op['after']==left,'right_identity');return
        x,y=left;u,v=right
        if x==u and (y+v)%P==0:
            require(kind=='inverse' and op['after'] is None,'inverse_case');return
        require(op['after'] is not None,'finite_result')
        slope=op['slope'];inverse=op['denominator_inverse'];scalar(slope);scalar(inverse)
        if left==right:
            require(kind=='double','double_case');den=2*y;num=3*x*x+2*a2*x+a4
        else:
            require(kind=='add' and u!=x,'add_case');den=u-x;num=v-y
        require((den*inverse)%P==1,'inverse_witness')
        require((den*slope-num)%P==0,'slope_equation')
        X,Y=op['after']
        require((X+a2+x+u-slope*slope)%P==0,'addition_x')
        require((Y+y-slope*(x-X))%P==0,'addition_y')
    mapped(c['base'],e['base']);require(c['base'] is not None,'nonidentity_base')
    bits=[int(b) for b in bin(R)[2:]];require(len(c['steps'])==len(bits)==len(e['steps']),'step_count')
    q=None;prefix=0;operations=0
    for bit,s,es in zip(bits,c['steps'],e['steps']):
        require(s['bit']==bit,'scalar_bit');prefix=2*prefix+bit;require(s['prefix']==prefix,'scalar_prefix')
        operation(q,q,s['doubling']);operations+=1;doubled=s['doubling']['after'];mapped(doubled,es['doubled'])
        if bit:
            require(s['addition'] is not None,'required_addition');operation(doubled,c['base'],s['addition']);operations+=1;q=s['addition']['after']
        else:
            require(s['addition'] is None,'no_extra_addition');q=doubled
        require(s['after']==q,'step_result');mapped(q,es['after'])
    require(prefix==R and q is None,'scalar_endpoint')
    return {'bits':len(bits),'operations':operations,'nonidentity_base':True,'infinity_endpoint':True,'all_edwards_maps_checked':True}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--candidate',type=Path,required=True);parser.add_argument('--edwards',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);a=parser.parse_args()
    started=time.monotonic();raw=a.edwards.read_bytes();require(hashlib.sha256(raw).hexdigest()==SOURCE,'source_file');e=json.loads(raw);c=json.loads(a.candidate.read_text());result=validate(c,e)
    def changed(path,value):
        m=copy.deepcopy(c);target=m
        for key in path[:-1]:target=target[key]
        target[path[-1]]=value
        return m
    s=c['steps'][1]['doubling']
    mutations=[('scalar_bit',changed(['steps',1,'bit'],0)),('prefix',changed(['steps',1,'prefix'],4)),
      ('inverse',changed(['steps',1,'doubling','denominator_inverse'],(s['denominator_inverse']+1)%P)),
      ('slope',changed(['steps',1,'doubling','slope'],(s['slope']+1)%P)),
      ('output_coordinate',changed(['steps',1,'doubling','after',0],(s['after'][0]+1)%P)),
      ('operation_case',changed(['steps',1,'doubling','case'],'add')),
      ('endpoint',changed(['steps',len(c['steps'])-1,'after'],c['base'])),('curve_parameter',changed(['a2'],(c['a2']+1)%P))]
    controls=[]
    for name,mutation in mutations:
        try:validate(mutation,e)
        except ValueError as err:controls.append({'case':name,'rejected':True,'reason':str(err)})
        else:raise RuntimeError('mutation accepted: '+name)
    result.update(kind='independent-arithmetic-data-validation-only',candidate_sha256=hashlib.sha256(a.candidate.read_bytes()).hexdigest(),controls=controls,elapsed_seconds=time.monotonic()-started,kernel_credit=0,group_law_credit=0,r_primality_credit=0,full_curve_order='OPEN',full_transfer='OPEN')
    with a.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result))
