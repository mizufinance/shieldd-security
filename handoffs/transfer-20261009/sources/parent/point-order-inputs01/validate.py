"""Independent data validation using multiplication identities, never modular inversion."""
import json,pathlib,copy,hashlib
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
R=6554484396890773809930967563523245729705921265872317281365359162392183254199
D=19257038036680949359750312669786877991949435402254120286184196891950884077233
BASE=[8076246640662884909881801758704306714034609987455869804520522091855516602923,13262374693698910701929044844600465831413122818447359594527400194675274060458]
def require(b,msg):
 if not b:raise ValueError(msg)
def point(a):
 require(isinstance(a,list) and len(a)==2 and all(type(x)==int and 0<=x<P for x in a),'coordinate range')
 x,y=a;require((y*y-x*x-1-D*x*x*y*y)%P==0,'curve equation')
def step(a,b,out,inv):
 point(out);require(isinstance(inv,list) and len(inv)==2 and all(type(x)==int and 0<=x<P for x in inv),'inverse range')
 x,y=a;u,v=b;ox,oy=out;ix,iy=inv;t=D*x*u*y*v%P
 require((1+t)*ix%P==1 and (1-t)*iy%P==1,'inverse equations')
 require((ox-(x*v+y*u)*ix)%P==0 and (oy-(y*v+x*u)*iy)%P==0,'addition equations')
def validate(d):
 require(d['schema']=='edwards-point-order-candidate-v1','schema')
 require((d['p'],d['r'],d['d'])==(P,R,D),'parameters');require(d['base']==BASE,'base identity');point(BASE);require(BASE!=[0,1],'nonidentity')
 bits=[int(x) for x in bin(R)[2:]];require(len(d['steps'])==len(bits),'length');prev=[0,1];prefix=0
 for bit,s in zip(bits,d['steps']):
  require(type(s['bit'])==int and s['bit']==bit,'scalar bit');prefix=2*prefix+bit;require(s['prefix']==prefix,'prefix')
  step(prev,prev,s['doubled'],s['doubling_inverses'])
  if bit:step(s['doubled'],BASE,s['after'],s['addition_inverses'])
  else:require(s['after']==s['doubled'] and s['addition_inverses'] is None,'zero bit')
  prev=s['after']
 require(prefix==R and prev==[0,1],'final identity')
 return {'steps':len(bits),'addition_steps':sum(bits),'total_point_operations':len(bits)+sum(bits)}
if __name__=='__main__':
 root=pathlib.Path(__file__).parent;p=root/'candidate.json';d=json.loads(p.read_text());counts=validate(d)
 controls=[]
 for name,mutate in [('changed_base',lambda x:x['base'].__setitem__(0,x['base'][0]+1)),('changed_bit',lambda x:x['steps'][1].__setitem__('bit',1-x['steps'][1]['bit'])),('changed_prefix',lambda x:x['steps'][2].__setitem__('prefix',0)),('changed_inverse',lambda x:x['steps'][0]['doubling_inverses'].__setitem__(0,0)),('changed_output',lambda x:x['steps'][1]['after'].__setitem__(0,0)),('missing_step',lambda x:x['steps'].pop()),('changed_order',lambda x:x.__setitem__('r',R-2)),('noncanonical_coordinate',lambda x:x['steps'][0]['doubled'].__setitem__(0,P))]:
  x=copy.deepcopy(d);mutate(x)
  try:validate(x)
  except ValueError as e:controls.append({'name':name,'rejected':True,'reason':str(e)})
  else:raise RuntimeError('accepted mutation '+name)
 result={'status':'passed','counts':counts,'controls':controls,'candidate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'proof_credit':0,'kernel_run':False};(root/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','counts':counts,'controls':len(controls),'candidate_sha256':result['candidate_sha256']}))
