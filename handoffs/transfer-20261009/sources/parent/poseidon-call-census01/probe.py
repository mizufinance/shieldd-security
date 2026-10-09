"""Bounded source-DAG analysis; no kernel or runtime-call correspondence credit."""
import json,sqlite3,pathlib,hashlib,time,resource,math
R=pathlib.Path(__file__).resolve().parents[2];O=pathlib.Path(__file__).parent
if not __debug__:raise RuntimeError('optimized mode forbidden')
resource.setrlimit(resource.RLIMIT_CPU,(60,60));start=time.monotonic()
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
D=R/'work/parent-full-program/capture/lowering-resume01.sqlite';db=sqlite3.connect(D.resolve().as_uri()+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16384')
def digest(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  while b:=s.read(1024**2):h.update(b)
 return h.hexdigest()
assert digest(D)=='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'
census=json.loads((R/'work/parent-poseidon-census01/result03.json').read_text());params={};inv={}
def inverse(m):
 n=len(m);a=[row[:]+[int(i==j) for j in range(n)] for i,row in enumerate(m)]
 for j in range(n):
  k=next(k for k in range(j,n) if a[k][j]);a[j],a[k]=a[k],a[j];v=pow(a[j][j],-1,p);a[j]=[v*x%p for x in a[j]]
  for i in range(n):
   if i!=j:
    v=a[i][j];a[i]=[(x-v*y)%p for x,y in zip(a[i],a[j])]
 return [row[n:] for row in a]
for w,f in [(3,'poseidon381.json'),(6,'poseidon381-wide.json')]:
 d=json.loads((R/'work/runtime-snapshot/crates/crypto/primitives/params'/f).read_text());params[w]=d;inv[w]=inverse([[int(v,16) for v in row] for row in d['mds']])
def add(a,b,scale=1):
 c=a.copy()
 for k,v in b.items():c[k]=(c.get(k,0)+scale*v)%p
 return {k:v for k,v in c.items() if v}
def scale(a,k):return {i:v*k%p for i,v in a.items() if v*k%p}
records=[];fail=[]
for m in census['matches']:
 cache={};const={};lin={};visited=set()
 def constant(i):
  if i not in const:const[i]=int(db.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0],16)
  return const[i]
 def node(i):
  if i not in cache:cache[i]=db.execute('SELECT op,lk,li,rk,ri FROM nodes WHERE id=?',(i,)).fetchone()
  visited.add(i);return cache[i]
 def linear(ref):
  k,i=ref
  if k==0:return {-1:constant(i)} if constant(i) else {}
  if k==1:return {('input',i):1}
  if i in lin:return lin[i]
  op,lk,li,rk,ri=node(i)
  if op=='add':v=add(linear((lk,li)),linear((rk,ri)))
  elif op=='sub':v=add(linear((lk,li)),linear((rk,ri)),-1)
  elif op=='mul' and lk==0:v=scale(linear((rk,ri)),constant(li))
  elif op=='mul' and rk==0:v=scale(linear((lk,li)),constant(ri))
  else:v={i:1}
  lin[i]=v;return v
 try:
  w=m['width'];forms=[linear(ref) for ref in m['input_ports']];sbox=[];before=[]
  for j,row in enumerate(inv[w]):
   form={}
   for coef,value in zip(row,forms):form=add(form,value,coef)
   ark=int(params[w]['ark'][0][j],16)
   if not form or set(form)=={-1}:
    x=pow(form.get(-1,0),pow(5,-1,p-1),p);before.append(['native',(x-ark)%p]);sbox.append(['native',form.get(-1,0)]);continue
   assert len(form)==1 and next(iter(form.values()))==1,('sbox expression',j,form)
   fifth=next(iter(form));assert isinstance(fifth,int) and fifth>=0
   op,lk,fourth,rk,x=node(fifth);assert op=='mul' and lk==rk==2
   op,lk,sq,rk,sq2=node(fourth);assert op=='mul' and lk==rk==2 and sq==sq2
   op,lk,x1,rk,x2=node(sq);assert op=='mul' and lk==rk==2 and x1==x2==x
   op,lk,ci,rk,ri=node(x);assert op=='add' and lk==0 and constant(ci)==ark
   before.append([rk,ri]);sbox.append([2,fifth])
  records.append({'width':w,'round1_span':m['nodes'],'after_round0':m['input_ports'],'before_round0':before,'sbox':sbox,'final_state':m['final_state'],'round0_visited_nodes':[min(visited),max(visited)],'round0_visited_count':len(visited)})
 except (AssertionError,KeyError,TypeError,StopIteration) as e:fail.append({'width':m['width'],'nodes':m['nodes'],'reason':str(e)})
 assert time.monotonic()-start<120 and resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<512*1024**2
assert digest(D)==census['database_sha256']
r={'kind':'exploratory-round0-source-decomposition-data-only','accepted':records,'failures':fail,'seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'database_sha256':census['database_sha256'],'proof_credit':0,'full_transfer':'OPEN'};(O/'probe01.json').write_text(json.dumps(r,indent=2)+'\n');print('accepted',len(records),'failures',len(fail),'seconds',r['seconds']);print(fail[:3]);print('native state0',sum(x['before_round0'][0][0]=='native' for x in records))
