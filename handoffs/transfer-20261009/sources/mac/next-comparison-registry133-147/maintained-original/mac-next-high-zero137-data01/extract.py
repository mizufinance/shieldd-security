from pathlib import Path
import sqlite3,json,hashlib,sys
S=Path(__file__).resolve().parent;W=S.parent;P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692
DB=W/'parent-full-program/capture/lowering-resume01.sqlite'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def canonical(ts):
 d={}
 for x,v in ts:d[x]=(d.get(x,0)+v)%P
 return [[x,v]for x,v in sorted(d.items())if v]
def scale(k,ts):return canonical([[x,k*v]for x,v in ts])
def outlined(ts):return sorted([[COPY if x==0 else x,v]for x,v in ts])
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated Python')
require(not(S/'selected-data01.json').exists(),'immutable qualification')
st=DB.stat();c=sqlite3.connect('file:'+str(DB)+'?mode=ro',uri=True);c.execute('pragma cache_size=-8192');c.execute('pragma query_only=on')
ns={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=json.loads(r[7]),certificate=json.loads(r[8]))for r in c.execute('select id,op,lk,li,rk,ri,kind,terms,certificate from nodes where id between 127698 and 128212')}
require(len(ns)==515,'complete zero-test source interval')
constants={};external={};arithmetic=[]
def operand(k,i):
 if k==0:
  if i not in constants:
   r=c.execute('select value from constants where id=?',(i,)).fetchone();require(r is not None,'allocated constant');v=int(r[0],16);require(0<=v<P,'canonical coefficient');constants[i]=v
  v=constants[i];return [[0,v]]if v else[]
 if k==1:return [[i+3,1]]
 require(k==2,'actual source role')
 if i not in ns:
  require(i<127698,'backward external dependency')
  r=c.execute('select kind,terms,certificate from nodes where id=?',(i,)).fetchone();require(r is not None and r[0]=='linear','external actual linear cut');external[i]=dict(kind=r[0],terms=json.loads(r[1]),certificate=json.loads(r[2]));return external[i]['terms']
 require(ns[i]['kind']=='linear','only linear node consumed');return ns[i]['terms']
for i,n in ns.items():
 cert=n['certificate'];require(cert['node']==i and cert['left']==[n['lk'],n['li']]and cert['right']==[n['rk'],n['ri']],'exact source operands')
 for k,j in [(n['lk'],n['li']),(n['rk'],n['ri'])]:require(k!=2 or j<i,'topological operand')
 left=operand(n['lk'],n['li']);right=operand(n['rk'],n['ri'])
 if n['op']=='add':require(cert['constructor']=='add'and n['kind']=='linear'and cert['rows']==[],'add kind');expected=canonical(left+right)
 elif cert['constructor']=='deferred':require(n['op']=='mul'and n['kind']=='square'and left==right and cert['rows']==[],'deferred exact square');expected=left
 elif cert['constructor']=='product':
  require(n['op']=='mul'and n['kind']=='linear'and i in [128209,128212],'exact two products');expected=n['terms'];require(expected==[[33778 if i==128209 else 33780,1]],'actual product write')
  auxiliary=cert['auxiliary'];require(auxiliary==[[33779 if i==128209 else 33781,1]],'actual auxiliary')
  for rowidx,a,b,role in [(cert['rows'][0],canonical(left+scale(-1,right)),auxiliary,'minus'),(cert['rows'][1],canonical(left+right),canonical(auxiliary+scale(4,expected)),'plus')]:
   raw=c.execute('select a,b,origin from rows where id=?',(rowidx,)).fetchone();ra,rb,origin=map(json.loads,raw);require(ra==a and rb==b and origin==dict(kind='node',id=i,role=role),'exact actual product row')
   arithmetic.append(dict(index=rowidx,a=ra,b=rb,outlined_a=outlined(ra),outlined_b=outlined(rb),origin=origin))
 else:
  require(n['op']=='mul'and n['kind']=='linear'and cert['rows']==[]and cert['constructor']in['foldedLeft','foldedRight'],'folded source multiplication');key='lk'if cert['constructor']=='foldedLeft'else'rk';ix='li'if key=='lk'else'ri';require(n[key]==0,'folded allocated coefficient');co=constants[n[ix]];require(cert['coefficient']==co,'certificate coefficient');expected=scale(co,right if key=='lk'else left)
 require(n['terms']==expected,'independent exact node LC')
delta=canonical([[854+i,2**i]for i in range(127)]+[[599+i,-2**i]for i in range(127)])
require(ns[128207]['terms']==delta,'actual next-high minus asset-high delta')
rows=[]
for j in range(3):
 idx=1333+j;ra=c.execute('select lk,li,rk,ri,certificate from assertions where id=?',(idx,)).fetchone();cert=json.loads(ra[4]);require(cert['assertion']==idx and cert['left']==[ra[0],ra[1]]and cert['right']==[ra[2],ra[3]]and cert['rows']==[177954+idx],'assertion source/position certificate')
 left=operand(ra[0],ra[1]) if j else ns[128208]['terms'];right=operand(ra[2],ra[3])
 if j==0:require(cert['constructor']=='squareLinear'and ns[128208]['kind']=='square','Boolean recipe');a,b=left,right;role='fusedSquare'
 else:require(cert['constructor']=='linear','linear recipe');a,b=canonical(left+scale(-1,right)),[];role='linear'
 raw=c.execute('select a,b,origin from rows where id=?',(177954+idx,)).fetchone();r_a,r_b,origin=map(json.loads,raw);require(r_a==a and r_b==b and origin==dict(kind='assertion',id=idx,role=role),'exact original assertion body/origin')
 rows.append(dict(index=177954+idx,assertion=idx,a=a,b=b,outlined_a=outlined(a),outlined_b=outlined(b),origin=origin,certificate=cert))
require([r['index']for r in arithmetic]==list(range(11040,11044)),'exact contiguous product positions')
require((st.st_size,st.st_mtime_ns)==(DB.stat().st_size,DB.stat().st_mtime_ns),'DB unchanged metadata')
d=dict(rows=rows,arithmetic_rows=arithmetic,source_nodes=len(ns),source_span=[127698,128212],source_node_lc_sha256=hashlib.sha256(json.dumps(ns,sort_keys=True,separators=(',',':')).encode()).hexdigest(),external_cuts=external,constants=constants,delta=delta,zero=1371,inverse=1372,write_window=[1371,1373],runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',database=dict(path=str(DB),bytes=st.st_size,mtime_ns=st.st_mtime_ns,historical_sha256='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'),binary_qualification=pin(W/'mac-full-arithmetic45-source01/qualification01.json'),range_source=pin(W/'runtime-snapshot/crates/crypto/circuits/src/range.rs'),registry_source=pin(W/'runtime-snapshot/crates/crypto/circuits/src/registry.rs'),scope='DATA only: two actual products11040..11043 and zero-test assertions179287..179289, actual next-high minus asset-high. Independent two-column field flag/inverse hints; no kernel/native claim.')
p=S/'selected-data01.json';p.write_text(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(dict(rows=len(rows),nodes=len(ns),constants=len(constants),selected=pin(p))))
