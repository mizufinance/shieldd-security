from pathlib import Path
import sys,json,hashlib,zlib,sqlite3,os
S=Path(__file__).resolve().parent;W=S.parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(v):
 p=Path(v['path']);require(pin(p)==v,'exact input');return json.loads(p.read_bytes())
def decoded(v):
 p=Path(v['path']);require(pin(p)==v,'exact compressed input');d=zlib.decompressobj();b=d.decompress(p.read_bytes(),1048577)
 require(len(b)<=1048576 and d.eof and not d.unconsumed_tail and not d.unused_data,'bounded compressed frame');return json.loads(b)
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'qualification01.json').exists(),'immutable qualification')
qa=json.loads((W/'mac-full-arithmetic45-source01/qualification01.json').read_bytes());qs=json.loads((W/'mac-assertion-provider50-source01/qualification01.json').read_bytes())
coeff=read(qa['coefficient_store'])['coefficients'];a=decoded(qa['chunks'][0]['data']);s=decoded(qs['chunks'][0]['data'])
def terms(x):return [[column,coeff[index]]for column,index in x]
rows=[];floor=a['low']
for r in a['recipes']:
 if r[1]==1:rows.append([terms(r[2]),[[floor,1]]]);floor+=1
 else:rows.extend([[terms(r[2]),[[floor+1,1]]],[terms(r[3]),[[floor,4],[floor+1,1]]]]);floor+=2
require(len(rows)==512,'qualified arithmetic span')
db=W/'parent-full-program/capture/lowering-resume01.sqlite';before=dict(bytes=db.stat().st_size,mtime_ns=db.stat().st_mtime_ns)
c=sqlite3.connect('file:'+str(db)+'?mode=ro&immutable=1',uri=True);c.execute('PRAGMA cache_size=-8192')
selected=[]
for index in [*range(256,262),*range(178044,178048)]:
 r=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(index,)).fetchone();require(r is not None,'actual selected row')
 original=[json.loads(r[0]),json.loads(r[1])];outlined=[sorted([[200692 if col==0 else col,k]for col,k in lc])for lc in original]
 if index<262:expected=rows[index]
 else:expected=[terms(lc)for lc in s['records'][index-177954]['actual']]
 require(outlined==expected,'exact original/body/outlining association')
 selected.append(dict(index=index,original=original,outlined=outlined,origin=json.loads(r[2])))
node_records=[]
for source in [426,429,430]:
 r=c.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(source,)).fetchone();require(r is not None and r[0]=='mul','actual product source')
 node_records.append(dict(source=source,op=r[0],left=[r[1],r[2]],right=[r[3],r[4]],kind=r[5],terms=json.loads(r[6]),certificate=json.loads(r[7])))
c.close();require(before==dict(bytes=db.stat().st_size,mtime_ns=db.stat().st_mtime_ns),'unchanged DB metadata')
config=json.loads((W/'mac-full-arithmetic45-execution12/config01.json').read_bytes());closure=read(config['closure'])['modules'];closure.update(config['qualified_batch_imports']);direct=[]
for n in ['CapturedArithmetic45B0000','CapturedAssertions50B0000','CompilerIndexed01']:
 v=closure[n]
 for key in ['source','object','receipt']:require(pin(Path(v[key]['path']))==v[key],'qualified direct '+key)
 direct.append(dict(module=n,qualified=v,fresh_execution_credit=0))
write('qualification01.json',dict(runtime=qa['runtime'],source_context=qa['source_context'],historical_db_sha256=qa['historical_db_sha256'],db=str(db),metadata=before,spool=qa['spool'],sidecar=qa['sidecar'],arithmetic_qualification=pin(W/'mac-full-arithmetic45-source01/qualification01.json'),assertion_qualification=pin(W/'mac-assertion-provider50-source01/qualification01.json'),compressed_inputs=[qa['chunks'][0]['data'],qs['chunks'][0]['data']],coefficient_store=qa['coefficient_store'],rows=selected,nodes=node_records,direct=direct,scope='DATA/SOURCE only; narrow read-only DB match to previously qualified full binary DATA. No new original stream replay, no kernel credit, no native/refinement conclusion.'))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()})
write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')))
write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(pin(S/'producer-manifest01.json'))
