from pathlib import Path
import sys,json,sqlite3,hashlib,struct
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not (S/'producer-manifest01.json').exists(),'no sealed refresh')
db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns)
c=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);c.execute('pragma query_only=on');c.execute('pragma cache_size=-8192')
rows=[];assertions=[];nodes=[]
for j in range(34):
 idx=178083+j;a,b,o=c.execute('select a,b,origin from rows where id=?',(idx,)).fetchone();a,b,o=json.loads(a),json.loads(b),json.loads(o)
 aid=129+j;lk,li,rk,ri,cert=c.execute('select lk,li,rk,ri,certificate from assertions where id=?',(aid,)).fetchone();cert=json.loads(cert)
 require(o['kind']=='assertion'and o['id']==aid and cert['assertion']==aid and cert['left']==[lk,li]and cert['right']==[rk,ri]and cert['rows']==[idx],'assertion identity')
 op,xk,xi,yk,yi,kind,terms,nc=c.execute('select op,lk,li,rk,ri,kind,terms,certificate from nodes where id=?',(li,)).fetchone();terms,nc=json.loads(terms),json.loads(nc)
 require(nc['node']==li and nc['left']==[xk,xi]and nc['right']==[yk,yi],'source node identity')
 if j<32:
  require(lk==2 and rk==1 and ri==181+j and cert['constructor']=='squareLinear','Boolean source roles')
  require(op=='mul'and kind=='square'and [xk,xi]==[1,181+j]and [yk,yi]==[1,181+j]and nc['constructor']=='deferred'and nc['rows']==[],'genuine deferred self-square')
  require(a==b==[[184+j,1]]and terms==a,'actual Boolean body')
 else:
  require(lk==2 and rk==1 and ri==132 and cert['constructor']=='linear'and kind=='linear','position assertion roles')
  require(terms==[[184+i,2**i]for i in range(32)]and a==[[135,P-1]]+terms and b==[],'actual exact weighted reconstruction')
 rows.append(dict(index=idx,a=a,b=b,origin=o));assertions.append(dict(id=aid,left=[lk,li],right=[rk,ri],certificate=cert));nodes.append(dict(id=li,op=op,left=[xk,xi],right=[yk,yi],kind=kind,terms=terms,certificate=nc))
c.close();require(before==(db.stat().st_size,db.stat().st_mtime_ns),'DB changed')
sp=R/'work/parent-full-program/capture/ordinary01.rows';h=hashlib.sha256();selected={};total=0
with sp.open('rb')as f:
 def exact(n):
  global total
  b=f.read(n);require(len(b)==n,'stream truncation');h.update(b);total+=n;return b
 def linear():
  n=struct.unpack('>Q',exact(8))[0];require(n<=32768,'term count');out=[];last=-1
  for _ in range(n):
   b=exact(36);i=struct.unpack('>I',b[:4])[0];v=int.from_bytes(b[4:],'big');require(last<i<262144 and 0<v<P,'canonical term');last=i;out.append([i,v])
  return out
 for idx in range(200770):
  row=[linear(),linear()]
  if 178083<=idx<178117:selected[idx]=row
 require(not f.read(1),'trailing stream')
require(total==86250856 and h.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9','qualified stream identity')
for r in rows:require(selected[r['index']]==[r['a'],r['b']],'exact original outlined body (no constants)')
cp=R/'work/parent-poseidon-call-census01/qualified01.json';out=dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',historical_db_sha=json.loads(cp.read_bytes())['database_sha256'],census=pin(cp),spool=dict(path=str(sp),bytes=total,sha256=h.hexdigest()),sidecar=pin(R/'work/parent-full-program/capture/ordinary01.shape.json'),primary_source=pin(R/'work/runtime-snapshot/crates/crypto/circuits/src/tree.rs'),rows=rows,assertions=assertions,nodes=nodes,status='DATA-only independently qualified actual deferred assertions; source position is original column135, bit hints184..215')
b=(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n').encode();p=S/'selected-data01.json'
if p.exists():require(p.read_bytes()==b,'immutable DATA')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(data=pin(p),rows=34,booleans=32,duplicate_reconstruction=2)))
