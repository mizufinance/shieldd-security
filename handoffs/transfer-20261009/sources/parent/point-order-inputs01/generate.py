"""Generate untrusted point-order certificate data from the pinned crate; no proof credit."""
import argparse,hashlib,json,pathlib,tarfile
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
R=6554484396890773809930967563523245729705921265872317281365359162392183254199
D=19257038036680949359750312669786877991949435402254120286184196891950884077233
CRATE='8499f7a74008aafbecb2a2e608a3e13e4dd3e84df198b604451efe93f2de6e61'
def add(a,b):
 x,y=a;u,v=b;t=D*x*u*y*v%P;ix=pow((1+t)%P,-1,P);iy=pow((1-t)%P,-1,P)
 return [(x*v+y*u)*ix%P,(y*v+x*u)*iy%P],[ix,iy]
def make(crate):
 if hashlib.sha256(crate.read_bytes()).hexdigest()!=CRATE:raise ValueError('crate hash mismatch')
 values={};refs=[]
 with tarfile.open(crate) as t:
  for n in ['p','l','a','d','x1','y1']:
   path='jubjub-0.10.0/doc/evidence/'+n;b=t.extractfile(path).read();values[n]=int(b)
   refs.append({'path':path,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 if (values['p'],values['l'],values['a'],values['d'])!=(P,R,-1,D):raise ValueError('parameter mismatch')
 base=[values['x1'],values['y1']];point=[0,1];prefix=0;steps=[]
 for bit in map(int,bin(R)[2:]):
  doubled,di=add(point,point)
  if bit:after,ai=add(doubled,base)
  else:after,ai=doubled,None
  prefix=2*prefix+bit;steps.append({'bit':bit,'prefix':prefix,'doubled':doubled,'doubling_inverses':di,'after':after,'addition_inverses':ai});point=after
 return {'schema':'edwards-point-order-candidate-v1','p':P,'r':R,'d':D,'base':base,'steps':steps,'crate_sha256':CRATE,'source_files':refs,'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','proof_credit':0,'claim':'Data for nonidentity on-curve point and r-fold repeated-addition identity only; primality, generic group semantics and full cardinality remain open.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--crate',required=True,type=pathlib.Path);ap.add_argument('--output',required=True,type=pathlib.Path);a=ap.parse_args();a.output.write_text(json.dumps(make(a.crate),indent=2)+'\n')
