from pathlib import Path
import sqlite3,json,hashlib,zlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=Path(__file__).parent/'data-replay01';DB=W/'parent-full-program/capture/lowering-resume01.sqlite'
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def strict(raw):
 def pairs(xs):
  out={}
  for k,v in xs:require(k not in out,'duplicate JSON');out[k]=v
  return out
 return json.loads(raw,object_pairs_hook=pairs)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def canonical(ts):
 out={}
 for col,v in ts:out[col]=(out.get(col,0)+v)%P
 return [[col,v]for col,v in sorted(out.items())if v]
def add(a,b):return canonical(a+b)
def scale(k,a):return canonical([[col,k*v]for col,v in a])
def outlined(a):return sorted([[COPY if col==0 else col,v]for col,v in a])
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not S.exists(),'fresh immutable DATA')
words=strict((W/'mac-word-slots211-source01/selected-data01.json').read_bytes())['selected']
selected=[(i,x)for i,x in enumerate(words)if x['width']==255]
bases=[116062,119123,122184,949489,973904,1096396,1099457,1102518,1105579,1116045,1119106,1122167,1125228,1166852]
require(len(selected)==len(bases)==14,'all actual255 words')
stat=DB.stat();c=sqlite3.connect('file:'+str(DB)+'?mode=ro',uri=True);c.execute('PRAGMA cache_size=-8192');c.execute('PRAGMA query_only=ON')
chains=[];constantRecords={};dbRows={}
for (wordIndex,slot),start in zip(selected,bases):
 end=start+9*255-1
 nodes={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=strict(r[7]),certificate=strict(r[8]))for r in c.execute('select id,op,lk,li,rk,ri,kind,terms,certificate from nodes where id between ? and ?',(start,end))}
 require(len(nodes)==2295,'complete255 nine-node constant comparison')
 def operand(kind,index):
  if kind==0:
   if index not in constantRecords:
    r=c.execute('select value from constants where id=?',(index,)).fetchone();require(r is not None,'constant present');constantRecords[index]=r[0]
   value=int(constantRecords[index],16);require(0<=value<P,'canonical constant');return []if value==0 else[[0,value]]
  if kind==1:return [[index+3,1]]
  require(kind==2 and index in nodes,'source backwards node');return nodes[index]['terms']
 entries=[];indices=[]
 for bitIndex in range(255):
  base=start+9*bitIndex;bit=(P-1)>>bitIndex&1
  expectedOps=['mul','add','mul','add','add','mul','add','mul','add']
  expectedRights=[(1,slot['start']-3+bitIndex),(2,base),(2,base+1),(2,base+1),(2,base+2),(2,base+4),(2,base+5),(2,base+6),(2,base+7)]
  for j in range(9):
   n=nodes[base+j];require(n['op']==expectedOps[j]and(n['rk'],n['ri'])==expectedRights[j]and n['kind']=='linear','exact source opcode/port/kind')
   if j in [0,1,2,3,5]:
    require(n['lk']==0,'allocated constant role');expected=[P-1,1,bit,bit,0,P-1][j];require(operand(n['lk'],n['li'])==([]if expected==0 else[[0,expected]]),'exact native constant')
   else:
    want={4:(2,base+2),6:(2,base+3),7:((0,n['li'])if bitIndex==0 else(2,base-1)),8:(2,base+2)}[j]
    require((n['lk'],n['li'])==want,'exact source left/carry')
    if j==7 and bitIndex==0:require(operand(n['lk'],n['li'])==[[0,1]],'initial flag1')
   left=operand(n['lk'],n['li']);right=operand(n['rk'],n['ri']);cert=n['certificate']
   require(cert['node']==n['id']and cert['left']==[n['lk'],n['li']]and cert['right']==[n['rk'],n['ri']],'exact source certificate')
   if n['op']=='add':
    expected=add(left,right);require(cert['constructor']=='add'and cert['rows']==[],'source add has no rows')
   elif j==7 and bitIndex>0:
    require(cert['constructor']=='product'and len(n['terms'])==1 and n['terms'][0][1]==1,'actual fresh product')
    pivot=n['terms'][0][0];aux=pivot+1;require(cert['auxiliary']==[[aux,1]]and len(cert['rows'])==2 and cert['rows'][1]==cert['rows'][0]+1,'exact product row pair')
    actual=[]
    for k,role,a,b in [(cert['rows'][0],'minus',add(left,scale(-1,right)),[[aux,1]]),(cert['rows'][1],'plus',add(left,right),[[pivot,4],[aux,1]])]:
     r=c.execute('select a,b,origin from rows where id=?',(k,)).fetchone();require(r is not None,'row present');a0,b0,origin=map(strict,r)
     require(a0==a and b0==b and origin==dict(kind='node',id=n['id'],role=role),'exact original product row body/origin')
     record=dict(index=k,a=outlined(a0),b=outlined(b0),origin=origin);dbRows[k]=record;actual.append(record);indices.append(k)
    entries.append(dict(bitColumn=slot['start']+bitIndex,maximumBit=bool(bit),before=outlined(left),after=outlined(nodes[base+8]['terms']),pivot=pivot,auxiliary=aux,rows=actual));expected=n['terms']
   else:
    if not left or not right:expected=[]
    elif n['lk']==0:expected=scale(left[0][1],right)
    elif n['rk']==0:expected=scale(right[0][1],left)
    else:raise RuntimeError('unexpected unfrozen product')
    require(cert['rows']==[]and cert['constructor']in ['foldedLeft','foldedRight'],'exact folded product')
   require(n['terms']==expected,'independent every-node LC normalization')
 require(len(entries)==254 and indices==list(range(indices[0],indices[0]+508)),'complete contiguous254 product pairs')
 require(entries[0]['before']==[[slot['start'],P-1],[COPY,1]],'folded first false-bit boundary')
 terminals=[]
 for aid,lk,li,rk,ri,certRaw in c.execute('select id,lk,li,rk,ri,certificate from assertions where (lk=2 and li=?)or(rk=2 and ri=?)',(end,end)):
  cert=strict(certRaw)
  if cert['constructor']!='linear':continue
  require((rk,ri)==(2,end)and lk==0 and operand(lk,li)==[[0,1]],'asserted terminal compare1')
  require(cert==dict(assertion=aid,left=[lk,li],right=[rk,ri],constructor='linear',rows=[177954+aid]),'exact terminal assertion certificate')
  r=c.execute('select a,b,origin from rows where id=?',(177954+aid,)).fetchone();a,b,origin=map(strict,r)
  require(a==canonical([[0,1]]+scale(-1,nodes[end]['terms']))and b==[]and origin==dict(kind='assertion',id=aid,role='linear'),'terminal row association')
  terminals.append(dict(position=aid,index=177954+aid,source=[lk,li,rk,ri],raw_output=nodes[end]['terms'],actual=[outlined(a),outlined(b)],certificate=cert))
 require(len(terminals)==1,'unique asserted canonical comparison terminal')
 chains.append(dict(word_index=wordIndex,slot=slot,source_span=[start,end],source_nodes_sha256=hashlib.sha256(json.dumps(nodes,sort_keys=True,separators=(',',':')).encode()).hexdigest(),entries=entries,row_start=indices[0],row_count=len(indices),terminal=terminals[0]))
require((stat.st_size,stat.st_mtime_ns)==(DB.stat().st_size,DB.stat().st_mtime_ns),'frozen readonly DB')
# Independently compare selected rows/recipes to exact qualified original-spool projections.
qPath=W/'mac-full-arithmetic45-source01/qualification01.json';q=strict(qPath.read_bytes());co=Path(q['coefficient_store']['path']);require(pin(co)==q['coefficient_store'],'exact coefficient store');coeff=strict(co.read_bytes())['coefficients'];pins={str(qPath):pin(qPath),str(co):pin(co)};matched=set()
for chunk in q['chunks']:
 if not any(chunk['start']<=k<chunk['start']+chunk['count']for k in dbRows):continue
 p=Path(chunk['data']['path']);require(pin(p)==chunk['data'],'hash before bounded decode');pins[str(p)]=chunk['data'];d=zlib.decompressobj();raw=d.decompress(p.read_bytes(),1048577)
 require(len(raw)<=1048576 and d.eof and not d.unused_data and not d.unconsumed_tail and len(raw)==chunk['decoded_bytes']and hashlib.sha256(raw).hexdigest()==chunk['decoded_sha256'],'exact bounded qualified original DATA')
 data=strict(raw);index=data['start'];column=data['low']
 for rec in data['recipes']:
  node,width,*lcs=rec;require(width in [1,2]and len(lcs)==width,'actual recipe shape')
  for j,lc in enumerate(lcs):
   if index+j in dbRows:
    want=dbRows[index+j];a=[[col,coeff[v]]for col,v in lc];b=[[column,1]]if width==1 else([[column+1,1]]if j==0 else[[column,4],[column+1,1]])
    require(want['a']==a and want['b']==b and want['origin']['id']==node,'qualified outlined spool/recipe exact selected parity');matched.add(index+j)
  index+=width;column+=width
 require(index==data['start']+data['count'],'complete selected chunk walk')
require(matched==set(dbRows)and len(matched)==14*508,'all7112 exact outlined arithmetic positions')
require(q['runtime']=='844389ee069e1fb2e576708842d0b389b4d9a44a'and q['source_context']=='cec1b30defc23497c8e9b30528dca12b09d328ea','fixed context')
for p in [W/'mac-word-slots211-source01/selected-data01.json',W/'runtime-snapshot/crates/crypto/circuits/src/encoding.rs',W/'runtime-snapshot/crates/crypto/circuits/src/range.rs']:pins[str(p)]=pin(p)
data=dict(chains=chains,runtime=q['runtime'],source_context=q['source_context'],historical_db_sha256=q['historical_db_sha256'],database_stat=[stat.st_size,stat.st_mtime_ns],spool=q['spool'],sidecar=q['sidecar'],constant_count=len(constantRecords),constants_sha256=hashlib.sha256(json.dumps(constantRecords,sort_keys=True,separators=(',',':')).encode()).hexdigest(),scope='DATA_ONLY. All14 exact canonical255 comparisons,32130 source nodes,7112 qualified outlined arithmetic rows,14 terminal assertion associations. No kernel/canonical/legal-input/native credit.')
raw=(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n').encode();require(len(raw)<=8*1024**2,'compact DATA decoded cap');packed=zlib.compress(raw,9)
S.mkdir();(S/'extract.py').write_bytes(Path(__file__).read_bytes());(S/'selected-data01.json.zlib').write_bytes(packed)
out=dict(data=pin(S/'selected-data01.json.zlib'),decoded_bytes=len(raw),decoded_sha256=hashlib.sha256(raw).hexdigest(),inputs=pins,chains=len(chains),rows=len(matched),source_nodes=14*2295,constants=len(constantRecords),extractor=pin(S/'extract.py'),scope=data['scope'])
(S/'qualification01.json').write_text(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n');(S/'producer-manifest01.json').write_text(json.dumps({p.name:pin(p)for p in S.iterdir()},sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(stage=str(S),chains=14,rows=len(matched),source_nodes=32130,data=out['data'],decoded_bytes=len(raw),qualification=pin(S/'qualification01.json'))))
