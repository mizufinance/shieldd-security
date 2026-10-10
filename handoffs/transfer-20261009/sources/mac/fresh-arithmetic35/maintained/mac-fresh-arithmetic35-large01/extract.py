from pathlib import Path
import sqlite3,struct,json,hashlib,sys,time
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692
START=11032;COUNT=4;LOW=33770

def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
require(not(S/'producer-manifest01.json').exists(),'no sealed refresh')
db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns);c=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);c.execute('pragma query_only=on');c.execute('pragma cache_size=-8192')
raw=[]
for i,a,b,o in c.execute('select id,a,b,origin from rows where id>=? and id<? order by id',(START,START+COUNT)):
 raw.append(dict(index=i,a=json.loads(a),b=json.loads(b),origin=json.loads(o)))
require(len(raw)==COUNT and [r['index']for r in raw]==list(range(START,START+COUNT)),'exact positions')
recipes=[];j=0
while j<COUNT:
 r=raw[j];origin=r['origin'];require(origin['kind']=='node' and origin['role']in('square','minus'),'materialized arithmetic')
 op,terms,cert=c.execute('select op,terms,certificate from nodes where id=?',(origin['id'],)).fetchone();terms,cert=json.loads(terms),json.loads(cert);require(op=='mul' and terms==[[LOW+j,1]]and cert['node']==origin['id'],'source materialized pivot')
 if origin['role']=='square':
  require(cert['constructor']=='square' and cert['rows']==[r['index']]and r['b']==[[LOW+j,1]],'square body')
  require(all(col<LOW+j for col,v in r['a']),'square support')
  recipes.append(dict(kind='square',relative=j,indices=[r['index']],node=origin['id']));j+=1
 else:
  require(j+1<COUNT,'closed pair boundary');p=raw[j+1]
  require(cert['constructor']=='product' and cert['rows']==[r['index'],p['index']]and p['origin']==dict(kind='node',id=origin['id'],role='plus'),'adjacent actual pair')
  require(r['b']==[[LOW+j+1,1]]and p['b']==[[LOW+j,4],[LOW+j+1,1]],'both output coefficients')
  require(all(col<LOW+j for col,v in r['a']+p['a']),'pair support before BOTH writes')
  recipes.append(dict(kind='pair',relative=j,indices=[r['index'],p['index']],node=origin['id']));j+=2
copy=c.execute('select a,b,origin from rows where id=200769').fetchone();copy=[json.loads(x)for x in copy];require(copy==[[[0,1],[COPY,P-1]],[],dict(kind='constantCopy',column=COPY)],'actual copy exception')
c.close();require(before==(db.stat().st_size,db.stat().st_mtime_ns),'DB stable')
expected={r['index']:[sorted([[COPY if col==0 else col,v]for col,v in r[k]])for k in('a','b')]for r in raw};expected[200769]=copy[:2]
sp=R/'work/parent-full-program/capture/ordinary01.rows';h=hashlib.sha256();total=0;selected={}
with sp.open('rb')as f:
 def exact(n):
  global total
  b=f.read(n);require(len(b)==n,'truncated framing');h.update(b);total+=n;return b
 def lc():
  n=struct.unpack('>Q',exact(8))[0];require(n<=32768,'term count');ts=[];last=-1
  for _ in range(n):
   z=exact(36);col=int.from_bytes(z[:4],'big');v=int.from_bytes(z[4:],'big');require(last<col<262144 and 0<v<P,'strict canonical coefficient/column');last=col;ts.append([col,v])
  return ts
 for i in range(200770):
  row=[lc(),lc()]
  if i in expected:require(row==expected[i],'exact original outlined body/position');selected[str(i)]=dict(a=row[0],b=row[1])
 require(not f.read(1),'trailing stream')
require(total==86250856 and h.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9','binary identity')
side=pin(R/'work/parent-full-program/capture/ordinary01.shape.json');require(side['sha256']=='bb5bb1ad221386cf87d1ce75aaff4d7ee3e148803f4abf082f9108dbd73683cb','exact shape pin')
d=dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',historical_database_sha='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d',database_stat=before,spool=dict(path=str(sp),bytes=total,sha256=h.hexdigest()),sidecar=side,raw_unoutlined=raw,actual_outlined=selected,recipes=recipes,start=START,count=COUNT,low=LOW,high=LOW+COUNT,scope='DATA row-native arithmetic constructor; no source-evaluation/gadget/Transfer/native claim')
with(S/'selected-data01.json').open('x')as f:f.write(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(data=pin(S/'selected-data01.json'),recipes=len(recipes),positions=COUNT+1)))
