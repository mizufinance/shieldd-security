"""Qualified actual assertion/link rows and raw assertion expression recipes.

DATA parity only: no source expression semantics or assertion truth is assumed.
"""
from pathlib import Path
import sys,sqlite3,struct,hashlib,json,zlib,time
S=Path(__file__).resolve().parent;R=S.parent.parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
COPY=200692;START=177954;END=200770
def require(ok,reason):
 if not ok:raise ValueError(reason)
def pin(path):
 b=path.read_bytes();return dict(path=str(path),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(data):
 def pairs(items):
  out={}
  for k,v in items:require(k not in out,'duplicate JSON key');out[k]=v
  return out
 return json.loads(data,object_pairs_hook=pairs)
def write(path,data):
 with path.open('xb')as f:f.write(data)
def canon(terms):
 out={}
 for col,val in terms:out[col]=(out.get(col,0)+val)%P
 return [[col,val]for col,val in sorted(out.items())if val]
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized interpreter')
require(not(S/'qualification01.json').exists()and not(S/'data').exists(),'no sealed refresh')
co=R/'work/mac-arithmetic-coefficients39-source01/coefficients01.json'
require(pin(co)['sha256']=='2de49e8a330defea76d11c36645b29a85f254c639166e71e286b3745cfa81332','exact coefficient store')
coefficients=strict(co.read_bytes())['coefficients'];old_count=len(coefficients);ids={v:i for i,v in enumerate(coefficients)}
def encode(terms):
 result=[]
 for col,v in terms:
  require(0<=col<200693 and 0<v<P,'bounded canonical coefficient/column')
  if v not in ids:ids[v]=len(coefficients);coefficients.append(v)
  result.append([col,ids[v]])
 return result
db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns)
c=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);c.execute('pragma query_only=on');c.execute('pragma cache_size=-8192')
dbrows=iter(c.execute('select id,a,b,origin from rows where id>=177954 order by id'))
def expression(ref):
 kind,index=ref
 if kind==0:
  found=c.execute('select value from constants where id=?',(index,)).fetchone();require(found is not None,'constant reference exists')
  v=int(found[0],16);require(0<=v<P,'canonical allocated constant');return ['linear',[]if v==0 else[[0,v]]]
 if kind==1:
  require(0<=index<22735,'original input domain');return ['linear',[[3+index,1]]]
 require(kind==2,'closed source reference kind')
 found=c.execute('select kind,terms from nodes where id=?',(index,)).fetchone();require(found is not None,'source node reference exists')
 form,terms=found;require(form in ['linear','square'],'closed source expression');terms=strict(terms)
 require(terms==canon(terms),'exact canonical source LC');return [form,terms]
sp=R/'work/parent-full-program/capture/ordinary01.rows';h=hashlib.sha256();physical=0;records=[];chunks=[];term_count=0;start=START;forms={'linear':0,'squareLinear':0};links=[];begin=time.monotonic();(S/'data').mkdir()
def flush():
 global start,records,term_count
 if not records:return
 value=dict(start=start,count=len(records),records=records,term_count=term_count)
 raw=(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode();require(len(raw)<=1048576,'bounded decoded assertion block')
 p=S/'data'/('block-'+str(len(chunks)).zfill(4)+'.json.zlib');write(p,zlib.compress(raw,9))
 chunks.append(dict(index=len(chunks),start=start,count=len(records),term_count=term_count,data=pin(p),decoded_bytes=len(raw),decoded_sha256=hashlib.sha256(raw).hexdigest()))
 start+=len(records);records=[];term_count=0
with sp.open('rb')as f:
 def exact(n):
  global physical
  b=f.read(n);require(len(b)==n,'truncated row stream');physical+=n;h.update(b);return b
 def lc():
  count=struct.unpack('>Q',exact(8))[0];require(count<=32768,'LC term cap');out=[];last=-1
  for _ in range(count):
   b=exact(36);col=int.from_bytes(b[:4],'big');v=int.from_bytes(b[4:],'big');require(last<col<262144 and 0<v<P,'canonical original stream');last=col;out.append([col,v])
  return out
 for i in range(END):
  actual=[lc(),lc()]
  if i<START:continue
  index,a,b,origin=next(dbrows);a,b,origin=strict(a),strict(b),strict(origin);require(index==i,'exact positional row origin')
  outlined=[sorted([[COPY if col==0 and i!=200769 else col,v]for col,v in ts])for ts in [a,b]]
  require(actual==outlined,'both actual outlined sides/DB exact parity')
  if i<200767:
   aid=i-START;found=c.execute('select lk,li,rk,ri,certificate from assertions where id=?',(aid,)).fetchone();require(found is not None,'assertion exists')
   lk,li,rk,ri,cert=found;cert=strict(cert);left=[lk,li];right=[rk,ri];x=expression(left);y=expression(right)
   ctor=cert['constructor'];require(cert==dict(assertion=aid,left=left,right=right,constructor=ctor,rows=[i]),'complete exact assertion certificate')
   require(origin==dict(kind='assertion',id=aid,role='linear'if ctor=='linear'else'fusedSquare'),'exact assertion row attribution')
   if ctor=='linear':
    require(x[0]==y[0]=='linear'and a==canon(x[1]+[[col,-v]for col,v in y[1]])and b==[],'raw linear assertion normalization')
   else:require(ctor=='squareLinear'and x[0]=='square'and y[0]=='linear'and [a,b]==[x[1],y[1]],'raw fused-square assertion body')
   forms[ctor]+=1
   record=dict(index=i,assertion=aid,constructor=ctor,left=left,right=right,x=encode(x[1]),y=encode(y[1]),actual=[encode(actual[0]),encode(actual[1])])
  else:
   expected={200767:[[[1,1],[22737,P-1]],[]],200768:[[[2,1],[9,P-1]],[]],200769:[[[0,1],[COPY,P-1]],[]]}[i]
   require(actual==expected,'exact verifier link/copy');record=dict(index=i,origin=origin,actual=[encode(actual[0]),encode(actual[1])]);links.append(record)
  terms=sum(len(v)for v in actual)+len(record.get('x',[]))+len(record.get('y',[]))
  if records and(len(records)>=256 or term_count+terms>4000):flush()
  records.append(record);term_count+=terms
 require(not f.read(1),'exact stream EOF')
flush();c.close();require(before==(db.stat().st_size,db.stat().st_mtime_ns),'stable bounded readonly DB')
require(physical==86250856 and h.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9','exact complete stream SHA')
require(start==END and forms=={'linear':11958,'squareLinear':10855},'complete assertion/link partition')
side=pin(R/'work/parent-full-program/capture/ordinary01.shape.json');require(side['sha256']=='bb5bb1ad221386cf87d1ce75aaff4d7ee3e148803f4abf082f9108dbd73683cb','sidecar pin')
write(S/'extra-coefficients01.json',(json.dumps(dict(old_store=pin(co),first_index=old_count,coefficients=coefficients[old_count:]),sort_keys=True,separators=(',',':'))+'\n').encode())
result=dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',database_stat=before,historical_db_sha256='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d',spool=dict(path=str(sp),bytes=physical,sha256=h.hexdigest()),sidecar=side,old_coefficients=pin(co),extra_coefficients=pin(S/'extra-coefficients01.json'),forms=forms,links=links,chunks=chunks,extractor=pin(Path(__file__)),seconds=time.monotonic()-begin,scope='DATA original outlined assertion/link position/body/source-reference parity; source evaluation and legal-input assertion truth remain OPEN; no kernel credit')
write(S/'qualification01.json',(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n').encode());print(json.dumps(dict(chunks=len(chunks),new_coefficients=len(coefficients)-old_count,data_bytes=sum(x['data']['bytes']for x in chunks),seconds=result['seconds'],qualification=pin(S/'qualification01.json'))))
