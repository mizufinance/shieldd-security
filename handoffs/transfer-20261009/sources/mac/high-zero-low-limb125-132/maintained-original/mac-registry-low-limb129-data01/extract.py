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
ns={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=json.loads(r[7]),certificate=json.loads(r[8]))for r in c.execute('select id,op,lk,li,rk,ri,kind,terms,certificate from nodes where id between 125890 and 126791')}
require(len(ns)==902,'complete high-limb source interval')
constants={}
def operand(k,i):
 if k==0:
  if i not in constants:
   r=c.execute('select value from constants where id=?',(i,)).fetchone();require(r is not None,'allocated constant');v=int(r[0],16);require(0<=v<P,'canonical coefficient');constants[i]=v
  v=constants[i];return [[0,v]]if v else[]
 if k==1:return [[i+3,1]]
 require(k==2 and i in ns,'backward internal dependency');require(ns[i]['kind']=='linear','only linear node consumed');return ns[i]['terms']
for i,n in ns.items():
 cert=n['certificate'];require(cert['node']==i and cert['left']==[n['lk'],n['li']]and cert['right']==[n['rk'],n['ri']]and cert['rows']==[],'exact source operands and no materialized rows')
 left=operand(n['lk'],n['li']);right=operand(n['rk'],n['ri'])
 if n['op']=='add':require(cert['constructor']=='add'and n['kind']=='linear','add kind');expected=canonical(left+right)
 elif cert['constructor']=='deferred':require(n['op']=='mul'and n['kind']=='square'and left==right,'deferred exact square');expected=left
 else:
  require(n['op']=='mul'and n['kind']=='linear'and cert['constructor']in['foldedLeft','foldedRight'],'folded source multiplication');key='lk'if cert['constructor']=='foldedLeft'else'rk';ix='li'if key=='lk'else'ri';require(n[key]==0,'folded allocated coefficient');co=constants[n[ix]];require(cert['coefficient']==co,'certificate coefficient');expected=scale(co,right if key=='lk'else left)
 require(n['terms']==expected,'independent exact node LC')
require(ns[126145]['terms']==[[471+i,2**i]for i in range(128)]and ns[126401]['terms']==[[216+i,2**i]for i in range(128)],'source-ordered asset/value low limbs')
rows=[]
for j in range(131):
 idx=1072+j;ra=c.execute('select lk,li,rk,ri,certificate from assertions where id=?',(idx,)).fetchone();cert=json.loads(ra[4]);require(cert['assertion']==idx and cert['left']==[ra[0],ra[1]]and cert['right']==[ra[2],ra[3]]and cert['rows']==[177954+idx],'assertion source/position certificate')
 if j<129:
  column=1112 if j==0 else 1113+j;expected_a=[[column,1]];expected_b=expected_a;require(cert['constructor']=='squareLinear','Boolean square recipe')
 else:
  require(cert['constructor']=='linear','linear recipe');expected_b=[]
  if j==129:expected_a=canonical([[1113,P-1]]+[[1114+i,2**i]for i in range(128)])
  else:expected_a=canonical([[216+i,2**i]for i in range(128)]+[[471+i,-2**i]for i in range(128)]+[[1112,2**128],[1113,-1]])
 r=c.execute('select a,b,origin from rows where id=?',(177954+idx,)).fetchone();a,b,origin=map(json.loads,r);require(a==expected_a and b==expected_b and origin==dict(kind='assertion',id=idx,role='fusedSquare'if j<129 else'linear'),'exact original row body/origin')
 rows.append(dict(index=177954+idx,assertion=idx,a=a,b=b,outlined_a=outlined(a),outlined_b=outlined(b),origin=origin,certificate=cert))
require((st.st_size,st.st_mtime_ns)==(DB.stat().st_size,DB.stat().st_mtime_ns),'DB unchanged metadata')
d=dict(rows=rows,source_nodes=len(ns),source_span=[125890,126791],source_node_lc_sha256=hashlib.sha256(json.dumps(ns,sort_keys=True,separators=(',',':')).encode()).hexdigest(),constants=constants,original_input_low_asset=[471,599],original_input_low_value=[216,344],borrow=1112,difference=1113,bits=[1114,1242],hints_write_window=[1112,1242],arithmetic_rows_allocated=0,runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',database=dict(path=str(DB),bytes=st.st_size,mtime_ns=st.st_mtime_ns,historical_sha256='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'),binary_qualification=pin(W/'mac-full-arithmetic45-source01/qualification01.json'),range_source=pin(W/'runtime-snapshot/crates/crypto/circuits/src/range.rs'),registry_source=pin(W/'runtime-snapshot/crates/crypto/circuits/src/registry.rs'),scope='DATA only: actual first128-bit bounded limb asset_low versus registry_value_low. Borrow Boolean,128 difference bits,reconstruction,balance:131 assertions179026..179156. No kernel truth/constructor/source-native claim.')
p=S/'selected-data01.json';p.write_text(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(dict(rows=len(rows),nodes=len(ns),constants=len(constants),selected=pin(p))))
