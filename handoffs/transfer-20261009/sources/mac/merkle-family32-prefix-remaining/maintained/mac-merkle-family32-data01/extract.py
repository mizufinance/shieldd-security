from pathlib import Path
import sys,json,sqlite3,hashlib,struct
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692
def require(x,m):
 if not x:raise ValueError(m)
def canon(ts):
 d={}
 for c,v in ts:d[c]=(d.get(c,0)+v)%P
 return [[c,v]for c,v in sorted(d.items())if v]
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists(),'no sealed refresh')
cp=R/'work/parent-poseidon-call-census01/qualified01.json';catalog=json.loads(cp.read_bytes());calls=[x for x in catalog['calls']if x['width']==6 and x['domain']==2 and x['arity']==5]
require(len(calls)==16,'actual first asset path length')
pp=R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json';require(pin(pp)['sha256']=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8','wide parameter identity');pr=json.loads(pp.read_bytes());parse=lambda x:int(x,16)if isinstance(x,str)and not x.isdecimal()else int(x);ark=[[parse(x)for x in row]for row in pr['ark']];mds=[[parse(x)for x in row]for row in pr['mds']]
db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns);co=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);co.execute('pragma query_only=on');co.execute('pragma cache_size=-8192')
def terms(ref):
 k,i=ref
 if k=='native':return canon([[0,i]])
 if k==0:return canon([[0,int(co.execute('select value from constants where id=?',(i,)).fetchone()[0],16)]])
 if k==1:require(0<=i<22735,'source input bound');return [[i+3,1]]
 require(k==2,'source role');kind,t=co.execute('select kind,terms from nodes where id=?',(i,)).fetchone();require(kind=='linear','linear state');return json.loads(t)
def node(i):
 op,lk,li,rk,ri,kind,t,c=co.execute('select op,lk,li,rk,ri,kind,terms,certificate from nodes where id=?',(i,)).fetchone();return dict(id=i,op=op,left=[lk,li],right=[rk,ri],kind=kind,terms=json.loads(t),certificate=json.loads(c))
def row(i):
 a,b,o=co.execute('select a,b,origin from rows where id=?',(i,)).fetchone();return dict(index=i,a=json.loads(a),b=json.loads(b),origin=json.loads(o))
def outline(r):return [sorted([[COPY if c==0 else c,v]for c,v in r[k]])for k in('a','b')]
reference=[row(i)for i in range(362,734)];refDesc=json.loads((R/'work/parent-poseidon-descriptor01/descriptor.json').read_bytes());levels=[];expected={}
for j,call in enumerate(calls):
 level=j+1;require(call['inputs'][0]==['native',level]and call['IV']==1282 and len(call['permutations'])==1,'actual level/domain/arity/IV')
 b=call['permutations'][0];block=next(x for x in catalog['blocks']if x['round0_span']==b['round0_span']);start=b['absorption_nodes'][0];end=b['round1_64_span'][0]+95
 require(b['absorption_nodes']==list(range(start,start+4))and b['round0_span']==[start+4,start+67]and b['round1_64_span'][0]==start+68,'source spans')
 records=[node(i)for i in range(start,end+1)];constants={}
 for n in records:
  c=n['certificate'];require(c['node']==n['id']and c['left']==n['left']and c['right']==n['right'],'raw/certificate operation ports')
  ctor=c['constructor'];require((n['op']=='add'and ctor=='add')or(n['op']=='mul'and ctor in('square','product','foldedLeft','foldedRight')),'raw opcode/constructor')
  for k,i in [n['left'],n['right']]:
   if k==0:constants[i]=terms([k,i])
  if ctor=='add':require(canon(terms(n['left'])+terms(n['right']))==n['terms'],'source add expression')
  if ctor in('foldedLeft','foldedRight'):
   native=n['left']if ctor=='foldedLeft'else n['right'];other=n['right']if ctor=='foldedLeft'else n['left'];v=terms(native);require(len(v)<=1 and all(c==0 for c,_ in v),'folded native role');scalar=v[0][1]if v else 0;require(canon([[c,scalar*x]for c,x in terms(other)])==n['terms'],'folded scalar expression')
 low=25472+424*j;rstart=2734+424*j;rows=[row(i)for i in range(rstart,rstart+40)];recipes=[]
 for r in rows:
  if r['origin']['role']=='plus':continue
  n=node(r['origin']['id']);c=n['certificate'];ctor=c['constructor'];require(n['op']=='mul'and ctor in('square','product'),'materialized constructor');pivot=n['terms'][0][0];require(n['terms']==[[pivot,1]],'numeric fresh pivot');left,right=terms(n['left']),terms(n['right']);require(all(col<pivot for col,v in left+right),'earlier dependency')
  if ctor=='square':require(left==right and canon(left)==r['a']and r['b']==[[pivot,1]]and c['rows']==[r['index']],'exact square')
  else:
   plus=row(r['index']+1);require(c['rows']==[r['index'],r['index']+1]and c['auxiliary']==[[pivot+1,1]],'product indices');require(r['a']==canon(left+[[c,-v]for c,v in right])and r['b']==[[pivot+1,1]]and plus['a']==canon(left+right)and plus['b']==[[pivot,4],[pivot+1,1]],'both exact product rows')
  recipes.append(dict(index=r['index'],node=n['id'],constructor=ctor,pivot=pivot,left=left,right=right))
 require(len(recipes)==30,'two native lane prefix count')
 bef=[terms(x)for x in block['before_round0']];shift0=[canon(bef[i]+[[0,ark[0][i]]])for i in range(6)];trans0=[terms(x)for x in block['sbox']];after0=[terms(x)for x in block['after_round0']];shift1=[terms([2,i])for i in range(start+68,start+74)];trans1=[[[low+18+4*i,1]]for i in range(6)];after1=[terms([2,start+103+12*i])for i in range(6)]
 for i in range(2):require(trans0[i]==canon([[0,pow(shift0[i][0][1],5,P)]]),'two native fifth powers')
 for i in range(6):
  require(canon([[c,v*mds[i][k]]for k in range(6)for c,v in trans0[k]])==after0[i],'R0 actual MDS');require(canon(after0[i]+[[0,ark[1][i]]])==shift1[i],'R1 actual ARK');require(canon([[c,v*mds[i][k]]for k in range(6)for c,v in trans1[k]])==after1[i],'R1 actual MDS')
 offset=424+424*j;rename=lambda ts:canon([[c+1988+offset if 23076<=c<23472 else c,v]for c,v in ts]);require(after1==[rename(terms(x))for x in refDesc['rounds'][2]['before']],'actual complete tail seam')
 tail=[row(i)for i in range(rstart+40,rstart+412)]
 for a,t in zip(reference,tail):require(rename(a['a'])==t['a']and rename(a['b'])==t['b'],'each of372 actual translated tail rows')
 result=terms(call['result']);require(result==rename(terms([2,5817])),'actual final word1')
 selection=[row(i)for i in range(rstart-12,rstart)];products=[]
 for i in range(6):
  minus=selection[2*i];plus=selection[2*i+1];n=node(minus['origin']['id']);c=n['certificate'];pivot=low-12+2*i;left,right=terms(n['left']),terms(n['right']);require(n['op']=='mul'and c['constructor']=='product'and c['left']==n['left']and c['right']==n['right']and c['rows']==[minus['index'],plus['index']]and n['terms']==[[pivot,1]]and c['auxiliary']==[[pivot+1,1]],'selection operation/operand/pivot');require(minus['a']==canon(left+[[c,-v]for c,v in right])and minus['b']==[[pivot+1,1]]and plus['a']==canon(left+right)and plus['b']==[[pivot,4],[pivot+1,1]],'selection row bodies');products.append(dict(node=n['id'],left=left,right=right,pivot=pivot,certificate=c))
 for r in rows+selection+tail:expected[r['index']]=outline(r)
 levels.append(dict(level=level,call=call,low=low,prefix_start=rstart,tail_offset=offset,before0=bef,shift0=shift0,trans0=trans0,after0=after0,shift1=shift1,trans1=trans1,after1=after1,rows=rows,recipes=recipes,result=result,selection=selection,selection_products=products,selection_outputs=[terms(x)for x in call['inputs'][1:]],qualification=dict(prefix_raw_span=[start,end],raw_nodes=len(records),raw_record_sha256=digest(records),referenced_constants=len(constants),constant_value_sha256=digest(constants),tail_actual_rows=372,tail_body_sha256=digest(tail),status='DATA-only; actual phase/selection bodies retained, borrowed tail identity checked for every row')))
sp=R/'work/parent-full-program/capture/ordinary01.rows';h=hashlib.sha256();total=0;seen=0
with sp.open('rb')as f:
 def exact(n):
  global total
  b=f.read(n);require(len(b)==n,'truncated binary');h.update(b);total+=n;return b
 def linear():
  n=struct.unpack('>Q',exact(8))[0];require(n<=32768,'binary term count');out=[];last=-1
  for _ in range(n):
   b=exact(36);c=struct.unpack('>I',b[:4])[0];v=int.from_bytes(b[4:],'big');require(last<c<262144 and 0<v<P,'canonical binary term');last=c;out.append([c,v])
  return out
 for idx in range(200770):
  r=[linear(),linear()]
  if idx in expected:require(r==expected[idx],'independent original RowSpool body');seen+=1
  if idx==200769:require(r==[[[0,1],[COPY,P-1]],[]],'actual copy exception')
 require(not f.read(1),'trailing binary')
require(seen==6784 and total==86250856 and h.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9','exact full binary qualification')
co.close();require(before==(db.stat().st_size,db.stat().st_mtime_ns),'database changed')
out=dict(runtime=catalog['runtime_sha'],historical_db_sha=catalog['database_sha256'],census=pin(cp),parameters=pin(pp),sidecar=pin(R/'work/parent-full-program/capture/ordinary01.shape.json'),source=pin(R/'work/runtime-snapshot/crates/crypto/circuits/src/tree.rs'),spool=dict(path=str(sp),bytes=total,sha256=h.hexdigest()),levels=levels,rows=[2722,9506],writes=[25460,32244],qualification='DATA-only16source-ordered initial asset-path levels; not kernel/fullparent/native credit')
b=(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n').encode();p=S/'selected-data01.json'
if p.exists():require(p.read_bytes()==b,'immutable DATA replay')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(data=pin(p),levels=16,actual_arithmetic_rows=6784,prefix_recipes=480,selection_products=96)))
