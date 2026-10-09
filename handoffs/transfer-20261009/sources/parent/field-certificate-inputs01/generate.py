import argparse, json, math, hashlib
from pathlib import Path
parser = argparse.ArgumentParser(description="Generate untrusted Lucas/curve-field certificate inputs. No formal proof credit.")
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
R=6554484396890773809930967563523245729705921265872317281365359162392183254199
# Deterministic 64-bit primality screening ONLY guides factorization. Final
# candidate certificate checks below use full recursive Lucas witnesses.
def screen(n):
 if n<2:return False
 for p in (2,3,5,7,11,13,17,19,23,29,31,37):
  if n%p==0:return n==p
 if n>=2**64: raise ValueError('screen restricted to uint64')
 s=0; d=n-1
 while d%2==0:s+=1;d//=2
 for a in (2,325,9375,28178,450775,9780504,1795265022):
  if a%n==0:continue
  x=pow(a,d,n)
  if x in (1,n-1):continue
  for _ in range(s-1):
   x=x*x%n
   if x==n-1:break
  else:return False
 return True
def rho(n):
 for c in range(1,33):
  x=y=2; g=1
  for _ in range(100000):
   x=(x*x+c)%n;y=(y*y+c)%n;y=(y*y+c)%n
   g=math.gcd(abs(x-y),n)
   if g!=1:break
  if 1<g<n:return g
 raise ValueError('bounded rho failed '+str(n))
def factors(n):
 if n==1:return []
 if n<2**64 and screen(n):return [n]
 for p in range(2,1000):
  if n%p==0:return [p]+factors(n//p)
 d=rho(n);return factors(d)+factors(n//d)
certs={}
def cert(n, fs=None):
 if str(n) in certs:return
 if n==2: certs[str(n)]={'n':n,'base':1,'factors':[],'residues':[]};return
 fs=sorted(fs if fs is not None else factors(n-1))
 if math.prod(fs)!=n-1: raise ValueError("factor product mismatch")
 for q in set(fs):cert(q)
 for a in range(2,10000):
  if pow(a,n-1,n)==1 and all(pow(a,(n-1)//q,n)!=1 for q in set(fs)):break
 else:raise ValueError('bounded Lucas witness search failed')
 certs[str(n)]={'n':n,'base':a,'factors':fs,'residues':[{'q':q,'exponent':(n-1)//q,'residue':pow(a,(n-1)//q,n)} for q in sorted(set(fs))]}
x=15132376222941642752
if P-1!=x*x*(x-1)*(x+1): raise ValueError("modulus polynomial mismatch")
fs=factors(x)*2+factors(x-1)+factors(x+1)
cert(P,fs)
d=(-10240*pow(10241,-1,P))%P
i=pow(5,(P-1)//4,P)
if i*i%P!=P-1 or pow(d,(P-1)//2,P)!=P-1: raise ValueError("curve parameter residue mismatch")
result={'kind':'untrusted certificate input; Python data validation only, NO Lean proof credit','modulus':P,'factorization':sorted(fs),'certificates':certs,'coefficient_d':d,'coefficient_d_equation_quotient':(10241*d+10240)//P,'imaginary':i,'imaginary_square_quotient':(i*i+1)//P,'nonsquare_exponent':(P-1)//2,'nonsquare_residue':pow(d,(P-1)//2,P)}
path=args.output
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'file':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'bytes':path.stat().st_size,'certificate_count':len(certs),'root_base':certs[str(P)]['base'],'root_factors':sorted(fs)}))
