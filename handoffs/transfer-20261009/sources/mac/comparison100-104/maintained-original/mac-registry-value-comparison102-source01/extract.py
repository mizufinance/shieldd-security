from pathlib import Path
import sqlite3,json,hashlib,sys
S=Path(__file__).resolve().parent;W=S.parent;P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692
DB=W/'parent-full-program/capture/lowering-resume01.sqlite'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(name,value):
 with(S/name).open('x')as f:f.write(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n')
def canonical(terms):
 d={}
 for x,v in terms:d[x]=(d.get(x,0)+v)%P
 return [[x,v]for x,v in sorted(d.items())if v]
def add(a,b):return canonical(a+b)
def scale(k,a):return canonical([[x,k*v]for x,v in a])
def outlined(a):return sorted([[COPY if x==0 else x,v]for x,v in a])
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated flags')
require(not(S/'selected-data01.json').exists(),'no refresh')
stat=DB.stat();c=sqlite3.connect('file:'+str(DB)+'?mode=ro',uri=True);c.execute('PRAGMA cache_size=-8192');c.execute('PRAGMA query_only=ON')
nodes={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=json.loads(r[7]),certificate=json.loads(r[8]))for r in c.execute('select id,op,lk,li,rk,ri,kind,terms,certificate from nodes where id between 116062 and 118356')}
require(len(nodes)==2295,'exact255 groups9 nodes')
const={};rows=[];entries=[];before=[[0,1]]
def operand(kind,index):
 if kind==0:
  if index not in const:
   r=c.execute('select value from constants where id=?',(index,)).fetchone();require(r is not None,'constant present');const[index]=r[0]
  value=int(const[index],16);require(0<=value<P,'canonical constant');return []if value==0 else[[0,value]]
 if kind==1:return [[index+3,1]]
 require(kind==2 and index in nodes,'source node operand');return nodes[index]['terms']
for i in range(255):
 base=116062+9*i;bit=(P-1)>>i&1
 expected_ops=['mul','add','mul','add','add','mul','add','mul','add']
 expected_rights=[(1,213+i),(2,base),(2,base+1),(2,base+1),(2,base+2),(2,base+4),(2,base+5),(2,base+6),(2,base+7)]
 for j in range(9):
  n=nodes[base+j];require(n['op']==expected_ops[j]and(n['rk'],n['ri'])==expected_rights[j]and n['kind']=='linear','exact forward opcode/right/kind')
  if j in [0,1,2,3,5]:
   require(n['lk']==0,'allocated constant role');value=operand(n['lk'],n['li']);expected=[P-1,1,bit,bit,0,P-1][j];require(value==([]if expected==0 else[[0,expected]]),'native coefficient exact')
  else:
   expected_left={4:(2,base+2),6:(2,base+3),7:((0,n['li'])if i==0 else(2,base-1)),8:(2,base+2)}[j]
   require((n['lk'],n['li'])==expected_left,'exact left/backwards source role')
   if j==7 and i==0:require(operand(n['lk'],n['li'])==[[0,1]],'initial comparison1')
  left=operand(n['lk'],n['li']);right=operand(n['rk'],n['ri']);cert=n['certificate'];require(cert['node']==n['id']and cert['left']==[n['lk'],n['li']]and cert['right']==[n['rk'],n['ri']],'certificate source operands')
  if n['op']=='add':expected=add(left,right);require(cert['constructor']=='add'and cert['rows']==[],'add no allocated rows')
  elif j==7 and i>0:
   pivot=32244+2*i;aux=pivot+1;require(n['terms']==[[pivot,1]]and cert['constructor']=='product'and cert['auxiliary']==[[aux,1]]and cert['rows']==[9506+2*i,9507+2*i],'exact product window');expected=n['terms']
   actual=[]
   for k,role,a,b in [(9506+2*i,'minus',add(left,scale(-1,right)),[[aux,1]]),(9507+2*i,'plus',add(left,right),[[pivot,4],[aux,1]])]:
    r=c.execute('select a,b,origin from rows where id=?',(k,)).fetchone();require(r is not None,'row present');a0,b0,origin=map(json.loads,r);require(a0==a and b0==b and origin==dict(kind='node',id=n['id'],role=role),'exactDBrow/productbinding');actual.append(dict(index=k,a=outlined(a0),b=b0,origin=origin));rows.append(actual[-1])
   entries.append(dict(bitColumn=216+i,maximumBit=bool(bit),before=outlined(left),after=outlined(nodes[base+8]['terms']),pivot=pivot,auxiliary=aux,rows=actual))
  else:
   if left==[]or right==[]:expected=[]
   elif n['lk']==0:expected=scale(left[0][1],right)
   elif n['rk']==0:expected=scale(right[0][1],left)
   else:raise ValueError('unhandled source product')
   require(cert['rows']==[]and cert['constructor']in['foldedLeft','foldedRight'],'exact finite folded product')
  require(n['terms']==expected,'independent every-node LC normalization')
 before=nodes[base+8]['terms']
require(len(entries)==254 and len(rows)==508 and [r['index']for r in rows]==list(range(9508,10016)),'exact complete254products508rows')
require(entries[0]['before']==[[216,P-1],[COPY,1]]and entries[-1]['after']==[[470,P-1],[32752,1],[COPY,1]],'initial/final LC')
require((DB.stat().st_size,DB.stat().st_mtime_ns)==(stat.st_size,stat.st_mtime_ns),'readonly frozen DB metadata')
put('selected-data01.json',dict(entries=entries,source_nodes=2295,source_span=[116062,118356],constant_ids=sorted(const),constants_sha256=hashlib.sha256(json.dumps(const,sort_keys=True,separators=(',',':')).encode()).hexdigest(),database=str(DB),database_stat=[stat.st_size,stat.st_mtime_ns],historical_db_sha256='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d',runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',binary_qualification=pin(W/'mac-full-arithmetic45-source01/qualification01.json'),source_encoding=pin(W/'runtime-snapshot/crates/crypto/circuits/src/encoding.rs'),source_comparison=pin(W/'runtime-snapshot/crates/crypto/circuits/src/range.rs'),scope='Narrow independently replayed DB source/constant/recipe/row/port DATA. Existing fullRowSpool qualification separately referenced; no fresh fullDB/binary hash or kernel claim. First folded bit0 has no allocated rows; i1..254 are products.'))
print(json.dumps(dict(entries=len(entries),rows=len(rows),constants=len(const),selected=pin(S/'selected-data01.json'))))
