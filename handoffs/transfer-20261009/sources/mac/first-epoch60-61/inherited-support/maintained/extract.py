from pathlib import Path
import sys,sqlite3,struct,hashlib,json,zlib,time
S=Path(__file__).resolve().parent;R=S.parent.parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692;N=177954;LOW=22738
MAX_TERMS=4000;MAX_ROWS=512

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
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized interpreter')
require(not(S/'qualification01.json').exists(),'no qualification refresh')
co=R/'work/mac-arithmetic-coefficients39-source01/coefficients01.json';require(pin(co)['sha256']=='2de49e8a330defea76d11c36645b29a85f254c639166e71e286b3745cfa81332','exact coefficient store');cs=strict(co.read_bytes())['coefficients'];ids={v:i for i,v in enumerate(cs)}
db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns)
c=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);c.execute('pragma query_only=on');c.execute('pragma cache_size=-8192');dbrows=iter(c.execute('select id,a,b,origin from rows where id<177954 order by id'))
sp=R/'work/parent-full-program/capture/ordinary01.rows';h=hashlib.sha256();physical=0;chunks=[];records=[];start=0;width=0;terms=0;squares=0;products=0;pending=None;source_nodes=0
(S/'data').mkdir();begin=time.monotonic()
def flush():
 global start,width,terms,records
 if not records:return
 value=dict(start=start,count=width,low=LOW+start,high=LOW+start+width,recipes=records,term_count=terms)
 raw=(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode();require(len(raw)<=1048576,'decoded leaf cap')
 p=S/'data'/('block-'+str(len(chunks)).zfill(4)+'.json.zlib');write(p,zlib.compress(raw,9));chunks.append(dict(index=len(chunks),start=start,count=width,term_count=terms,recipes=len(records),data=pin(p),decoded_bytes=len(raw),decoded_sha256=hashlib.sha256(raw).hexdigest()))
 start+=width;width=0;terms=0;records=[]
with sp.open('rb')as f:
 def exact(n):
  global physical
  b=f.read(n);require(len(b)==n,'truncated stream');physical+=n;h.update(b);return b
 def lc():
  count=struct.unpack('>Q',exact(8))[0];require(count<=32768,'LC term cap');out=[];last=-1
  for _ in range(count):
   b=exact(36);col=int.from_bytes(b[:4],'big');v=int.from_bytes(b[4:],'big');require(last<col<262144 and 0<v<P,'canonical columns/coefficients');last=col;out.append([col,v])
  return out
 for i in range(200770):
  actual=[lc(),lc()]
  if i<N:
   index,a,b,origin=next(dbrows);require(index==i,'exact DB position');a,b,origin=strict(a),strict(b),strict(origin)
   outlined=sorted([[COPY if col==0 else col,v]for col,v in a]);require(actual==[outlined,b],'actual original outlined body/DB parity')
   require(origin['kind']=='node','arithmetic origin')
   role=origin['role'];node=origin['id'];pivot=LOW+i
   require(role in ['square','minus','plus'],'exact materialized role')
   if role=='plus':
    require(pending is not None and pending['node']==node and pending['index']+1==i,'adjacent matching plus')
    require(b==[[pivot-1,4],[pivot,1]] and all(col<pivot-1 for col,v in a),'plus output/support')
    pair_terms=pending['terms']+len(outlined)
    if records and (width+2>MAX_ROWS or terms+pair_terms>MAX_TERMS):flush()
    records.append([node,2,pending['encoded'],[[col,ids[v]]for col,v in outlined]]);width+=2;terms+=pair_terms;products+=1;pending=None
   else:
    op,node_terms,cert=c.execute('select op,terms,certificate from nodes where id=?',(node,)).fetchone();node_terms,cert=strict(node_terms),strict(cert)
    require(op=='mul'and node_terms==[[pivot,1]]and cert['node']==node,'raw operation/source output')
    require(all(col<pivot for col,v in a),'all input support before first write')
    source_nodes+=1
    encoded=[[col,ids[v]]for col,v in outlined]
    if role=='square':
     require(pending is None and cert['constructor']=='square'and cert['rows']==[i]and b==[[pivot,1]],'square source/row certificate')
     if records and (width+1>MAX_ROWS or terms+len(outlined)>MAX_TERMS):flush()
     records.append([node,1,encoded]);width+=1;terms+=len(outlined);squares+=1
    else:
     require(pending is None and cert['constructor']=='product'and cert['rows']==[i,i+1]and b==[[pivot+1,1]],'product source/minus certificate')
     pending=dict(index=i,node=node,terms=len(outlined),encoded=encoded)
  elif i==200769:require(actual==[[[0,1],[COPY,P-1]],[]],'actual constant copy body')
 require(not f.read(1),'exact stream EOF')
require(pending is None,'no unfinished pair');flush();c.close()
require(before==(db.stat().st_size,db.stat().st_mtime_ns),'stable bounded readonly DB')
require(physical==86250856 and h.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9','exact full binary pin')
require(start==N and squares==50478 and products==63738 and source_nodes==squares+products,'complete origin partition')
require(sum(x['term_count']for x in chunks)==1988002,'complete original a-LC term census')
side=pin(R/'work/parent-full-program/capture/ordinary01.shape.json');require(side['sha256']=='bb5bb1ad221386cf87d1ce75aaff4d7ee3e148803f4abf082f9108dbd73683cb','sidecar pin')
result=dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',database_stat=before,historical_db_sha256='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d',spool=dict(path=str(sp),bytes=physical,sha256=h.hexdigest()),sidecar=side,coefficient_store=pin(co),squares=squares,products=products,arithmetic_positions=N,write_window=[LOW,COPY],chunks=chunks,seconds=time.monotonic()-begin,scope='DATA exact all arithmetic row bodies/source op/certificate constructor/support parity; no kernel/global semantic credit')
write(S/'qualification01.json',(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n').encode());print(json.dumps(dict(chunks=len(chunks),bytes=sum(x['data']['bytes']for x in chunks),seconds=result['seconds'],qualification=pin(S/'qualification01.json'))))
