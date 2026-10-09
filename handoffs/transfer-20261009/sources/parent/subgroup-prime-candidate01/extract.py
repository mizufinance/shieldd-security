"""Parse pinned ACL2 Pratt certificate as data; complete small leaves for Lean Lucas replay."""
import pathlib,json,re,hashlib,math,time
if not __debug__:raise RuntimeError('optimized mode forbidden')
P=pathlib.Path(__file__).parent;start=time.monotonic();source=P/'jubjub-subgroup-prime.lisp'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='7d25bdffec279fa22a3fd87d8e490bfc66515c313e637edc93b9686c79bde32a'
s=re.sub(r';[^\n]*','',source.read_text());tokens=re.findall(r'\(|\)|[^\s()]+',s);index=0
def parse():
 global index
 t=tokens[index];index+=1
 if t!='(':return int(t) if t.isdecimal() else t
 out=[]
 while tokens[index]!=')':out.append(parse())
 index+=1;return out
forms=[]
while index<len(tokens):forms.append(parse())
f=next(x for x in forms if isinstance(x,list) and x and x[0]=='defprime');assert len(f)==4 and f[1]=='jubjub-subgroup-prime'
root=f[2];assert root==6554484396890773809930967563523245729705921265872317281365359162392183254199
certs={};origins={}
def factor(n):
 out=[];d=2
 while d*d<=n:
  while n%d==0:out.append(d);n//=d
  d=3 if d==2 else d+2
 if n>1:out.append(n)
 return out

def visit(n,tree):
 if n in certs:return
 if not tree:
  assert n<1000000
  factors=factor(n-1);base=1 if n==2 else next(b for b in range(2,10000) if pow(b,n-1,n)==1 and all(pow(b,(n-1)//q,n)!=1 for q in set(factors)))
  for q in sorted(set(factors)):visit(q,[])
  origin='small leaf completed by bounded trial factoring of n-1 and modular search'
 else:
  assert len(tree)==4;base,primes,exponents,children=tree;assert len(primes)==len(exponents)==len(children)
  assert all(isinstance(e,int) and 0<e<100 for e in exponents)
  factors=[q for q,e in zip(primes,exponents) for _ in range(e)]
  for q,child in zip(primes,children):assert 1<q<n;visit(q,child)
  origin='pinned ACL2 explicit certificate node'
 assert math.prod(factors)==n-1 and pow(base,n-1,n)==1
 residues=[{'q':q,'exponent':(n-1)//q,'residue':pow(base,(n-1)//q,n)} for q in sorted(set(factors))]
 assert all(x['residue']!=1 for x in residues)
 certs[n]={'n':n,'base':base,'factors':factors,'residues':residues};origins[str(n)]=origin
visit(root,f[3])
data={'kind':'candidate recursive Lucas certificate, no Lean credit','subgroup_order':root,'source_certificate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'certificates':{str(n):certs[n] for n in sorted(certs)},'origins':origins,'root_factorization':certs[root]['factors'],'kernel_run':False,'primality_credit':0};out=P/'candidate.json';out.write_text(json.dumps(data,indent=2)+'\n');print('nodes',len(certs),'sha256',hashlib.sha256(out.read_bytes()).hexdigest(),'seconds',time.monotonic()-start)
