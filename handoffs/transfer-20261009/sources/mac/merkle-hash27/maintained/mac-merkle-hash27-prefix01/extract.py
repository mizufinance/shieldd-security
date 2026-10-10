from pathlib import Path
import sys,json,hashlib,sqlite3,struct
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;C=200692
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def canon(ts):
 d={}
 for c,v in ts:d[c]=(d.get(c,0)+v)%P
 return [[c,v]for c,v in sorted(d.items())if v]
def write(p,d):
 b=(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode()
 if p.exists():require(p.read_bytes()==b,'immutable DATA')
 else:
  with p.open('xb')as f:f.write(b)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized')
require(not(S/'producer-manifest01.json').exists(),'no sealed DATA refresh')
cp=R/'work/parent-poseidon-call-census01/qualified01.json';d=json.loads(cp.read_bytes());block=next(b for b in d['blocks']if b['round0_span']==[29166,29229]);call=next(c for c in d['calls']if c['result']==[2,34470]);require(call['domain']==2 and call['arity']==5 and call['IV']==1282,'actual call')
pp=R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json';require(pin(pp)['sha256']=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8','wide parameters');params=json.loads(pp.read_bytes());parse=lambda x:int(x,16)if isinstance(x,str)and not x.isdecimal()else int(x);ark=[[parse(x)for x in r]for r in params['ark']];mds=[[parse(x)for x in r]for r in params['mds']]
db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns);co=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);co.execute('pragma query_only=on');co.execute('pragma cache_size=-8192')
def terms(ref):
 k,i=ref
 if k=='native':return canon([[0,i]])
 if k==0:return canon([[0,int(co.execute('select value from constants where id=?',(i,)).fetchone()[0],16)]])
 if k==1:return [[3+i,1]]
 require(k==2,'role');kind,t=co.execute('select kind,terms from nodes where id=?',(i,)).fetchone();require(kind=='linear','linear state');return json.loads(t)
def nr(i):
 op,lk,li,rk,ri,kind,t,c=co.execute('select op,lk,li,rk,ri,kind,terms,certificate from nodes where id=?',(i,)).fetchone();return dict(id=i,op=op,left=[lk,li],right=[rk,ri],kind=kind,terms=json.loads(t),certificate=json.loads(c))
records=[nr(i)for i in range(29162,29326)];constants={}
for n in records:
 c=n['certificate'];require(c['node']==n['id']and c['left']==n['left']and c['right']==n['right'],'raw/certificate identity')
 ctor=c['constructor'];require((n['op']=='add'and ctor=='add')or(n['op']=='mul'and ctor in ('square','product','foldedLeft','foldedRight')),'raw op/constructor')
 for k,i in [n['left'],n['right']]:
  if k==0:constants[i]=terms([k,i])
 if ctor=='add':require(canon(terms(n['left'])+terms(n['right']))==n['terms'],'exact addition expression')
 if ctor=='foldedLeft':require(len(terms(n['left']))==1 and terms(n['left'])[0][0]==0,'native left');require(canon([[x,terms(n['left'])[0][1]*v]for x,v in terms(n['right'])])==n['terms'],'folded native expression')
rows=[];recipes=[]
for i,a,b,o in co.execute('select id,a,b,origin from rows where id between 2734 and 2773 order by id'):
 a,b,o=json.loads(a),json.loads(b),json.loads(o);rows.append(dict(index=i,a=a,b=b,origin=o))
 if o['role']=='plus':continue
 n=nr(o['id']);c=n['certificate'];ctor=c['constructor'];require(n['op']=='mul'and ctor in('square','product'),'materialized operation');pivot=n['terms'][0][0];require(n['terms']==[[pivot,1]],'fresh unit output');l,r=terms(n['left']),terms(n['right']);require(all(col<pivot for col,v in l+r),'earlier dependencies')
 if ctor=='square':require(l==r and canon(l)==a and b==[[pivot,1]]and c['rows']==[i],'square row')
 else:
  require(c['rows']==[i,i+1]and c['auxiliary']==[[pivot+1,1]]and a==canon(l+[[col,-v]for col,v in r])and b==[[pivot+1,1]],'product minus')
  aa,bb=co.execute('select a,b from rows where id=?',(i+1,)).fetchone();require(json.loads(aa)==canon(l+r)and json.loads(bb)==[[pivot,4],[pivot+1,1]],'product plus')
 recipes.append(dict(row=i,node=n['id'],constructor=ctor,pivot=pivot,left=l,right=r))
require(len(rows)==40 and len(recipes)==30,'actual prefix sizes')
before0=[terms(x)for x in block['before_round0']];shift0=[canon(before0[i]+[[0,ark[0][i]]])for i in range(6)];trans0=[terms(x)for x in block['sbox']];after0=[terms(x)for x in block['after_round0']];shift1=[terms([2,i])for i in range(29230,29236)];trans1=[[[25490+4*i,1]]for i in range(6)];after1=[terms([2,i])for i in (29265,29277,29289,29301,29313,29325)]
for i in range(2):require(trans0[i]==canon([[0,pow(shift0[i][0][1],5,P)]]),'native fifth')
for i in range(6):
 require(canon([[c,v*mds[i][j]]for j in range(6)for c,v in trans0[j]])==after0[i],'R0 actual MDS')
 require(canon(after0[i]+[[0,ark[1][i]]])==shift1[i],'R1 actual ARK')
 require(canon([[c,v*mds[i][j]]for j in range(6)for c,v in trans1[j]])==after1[i],'R1 actual MDS')
ref=json.loads((R/'work/parent-poseidon-descriptor01/descriptor.json').read_bytes());rename=lambda ts:canon([[c+1988+424 if 23076<=c<23472 else c,v]for c,v in ts]);require(after1==[rename(terms(x))for x in ref['rounds'][2]['before']],'exact tail boundary')
# The source template window and disjoint swap have identical translation on these ports/rows.
for old,new in zip(range(362,734),range(2774,3146)):
 a,b=co.execute('select a,b from rows where id=?',(old,)).fetchone();aa,bb=co.execute('select a,b from rows where id=?',(new,)).fetchone();require(rename(json.loads(a))==json.loads(aa)and rename(json.loads(b))==json.loads(bb),'all target tail actual rows')
co.close();require((db.stat().st_size,db.stat().st_mtime_ns)==before,'DB changed')
sp=R/'work/parent-full-program/capture/ordinary01.rows';h=hashlib.sha256();selected={}
with sp.open('rb')as f:
 def exact(n):
  b=f.read(n);require(len(b)==n,'stream truncation');h.update(b);return b
 def linear():
  count=struct.unpack('>Q',exact(8))[0];require(count<=32768,'framing count');out=[];prev=-1
  for _ in range(count):
   b=exact(36);col=struct.unpack('>I',b[:4])[0];v=int.from_bytes(b[4:],'big');require(prev<col<262144 and 0<v<P,'canonical framing');out.append([col,v]);prev=col
  return out
 for i in range(200770):
  rr=[linear(),linear()]
  if 2734<=i<2774 or i==200769:selected[str(i)]=rr
 require(not f.read(1),'stream trailing')
require(h.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9','stream identity')
for x in rows:require(selected[str(x['index'])]==[sorted([[C if c==0 else c,v]for c,v in x[k]])for k in('a','b')],'actual outlined stream')
require(selected['200769']==[[[0,1],[C,P-1]],[]],'copy exception')
write(S/'selected-data01.json',dict(runtime=d['runtime_sha'],historical_db_sha=d['database_sha256'],census=pin(cp),parameters=pin(pp),spool=pin(sp),sidecar=pin(R/'work/parent-full-program/capture/ordinary01.shape.json'),call=call,block=block,records=records,constants=constants,rows=rows,recipes=recipes,originals=selected,before0=before0,shift0=shift0,trans0=trans0,after0=after0,shift1=shift1,trans1=trans1,after1=after1,tail_rows=[2774,3146],tail_swap=dict(start=25064,width=396,offset=424),status='qualified DATA only'))
print('qualified40 prefix rows/30 materialized steps;372 tail row transport; no kernel credit')
