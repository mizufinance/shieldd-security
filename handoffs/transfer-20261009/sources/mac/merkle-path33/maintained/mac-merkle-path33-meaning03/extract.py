from pathlib import Path
import sqlite3,json,hashlib,sys,struct
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent;P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags');require(not(S/'producer-manifest01.json').exists(),'sealed refresh')
D=R/'work/mac-merkle-family32-data01/selected-data01.json';dp=pin(D);require(dp['sha256']=='54d0de34d64a281643185ec9e85f00cb4ad78e5f992680babd50dd9ed780a03f','DATA pin');data=json.loads(D.read_bytes())
p=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(p.stat().st_size,p.stat().st_mtime_ns);c=sqlite3.connect(p.as_uri()+'?mode=ro',uri=True);c.execute('PRAGMA query_only=ON');c.execute('PRAGMA cache_size=-8192')
a,b,o=c.execute('SELECT a,b,origin FROM rows WHERE id=178117').fetchone();a,b,o=map(json.loads,(a,b,o));r=c.execute('SELECT lk,li,rk,ri,certificate FROM assertions WHERE id=163').fetchone();cert=json.loads(r[4]);kind,t,nc=c.execute('SELECT kind,terms,certificate FROM nodes WHERE id=115245').fetchone();t,nc=json.loads(t),json.loads(nc)
require(o=={'kind':'assertion','id':163,'role':'linear'} and list(r[:4])==[2,115245,1,1] and cert['constructor']=='linear'and cert['rows']==[178117],'anchor source/index');require(kind=='linear'and nc['constructor']=='add'and nc['rows']==[]and t==data['levels'][-1]['result'],'source result LC');require(a==[[4,P-1]]+t and b==[],'unoutlined anchor');c.close();require(before==(p.stat().st_size,p.stat().st_mtime_ns),'DB stability')
sp=Path(data['spool']['path']);h=hashlib.sha256();total=0;selected=None
with sp.open('rb')as f:
 def exact(n):
  global total
  v=f.read(n);require(len(v)==n,'truncation');h.update(v);total+=n;return v
 def lc():
  n=struct.unpack('>Q',exact(8))[0];require(n<=32768,'term bound');out=[];last=-1
  for _ in range(n):
   z=exact(36);i=struct.unpack('>I',z[:4])[0];v=int.from_bytes(z[4:],'big');require(last<i<262144 and 0<v<P,'canonical coefficient/index');last=i;out.append([i,v])
  return out
 for i in range(200770):
  row=[lc(),lc()]
  if i==178117:selected=row
 require(not f.read(1),'trailing')
require(total==data['spool']['bytes']and h.hexdigest()==data['spool']['sha256']and selected==[a,b],'original binary body/position')
out=dict(runtime=data['runtime'],historical_db_sha=data['historical_db_sha'],source_data=dp,spool=data['spool'],sidecar=data['sidecar'],tree_source=data['source'],index=178117,assertion=cert,origin=o,raw_result=115245,result=t,actual_row=dict(a=a,b=b),status='DATA only: actual anchor assertion/captured result; not native semantic correspondence or full relation')
with(S/'selected-data01.json').open('x')as f:json.dump(out,f,sort_keys=True,separators=(',',':'));f.write('\n')
print(pin(S/'selected-data01.json'))
