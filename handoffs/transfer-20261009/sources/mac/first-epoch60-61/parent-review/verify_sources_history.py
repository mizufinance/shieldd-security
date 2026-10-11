"""Independent source replay, literal DATA association and preserved failed history."""
from pathlib import Path
import json,hashlib,re,shutil,subprocess,zlib,sqlite3
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-first-epoch60-61-kernel-result01'
checked={}
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(r):
 assert pin(r['path'])==r,r;checked[r['path']]=r;return Path(r['path']).read_bytes()
stages=[]
for name,module,gen,count in [('mac-first-epoch-range60-source02','CapturedEpochRange60','generate02.py',18),('mac-first-epoch-nonzero61-source04','CapturedEpochNonzero61','generate.py',24)]:
 s=W/name
 for r in json.loads((s/'producer-manifest01.json').read_bytes()).values():read(r)
 d=J/(name+'-replay01');d.mkdir();shutil.copyfile(s/gen,d/gen);shutil.copyfile(s/'template.lean',d/'template.lean')
 run=subprocess.run(['python3','-I','-B','-S',str(d/gen)],capture_output=True);assert run.returncode==0,run.stderr
 p=s/'source-root/ShielddSecurity'/(module+'.lean');assert (d/'source-root/ShielddSecurity'/(module+'.lean')).read_bytes()==p.read_bytes()
 names=re.findall(r'^#check @([\w.]+)$',p.read_text(),re.M);assert len(names)==count
 assert re.findall(r'^#print axioms ([\w.]+)$',p.read_text(),re.M)==names
 stages.append(dict(stage=name,source=pin(p),exact_generator_replay=True,reports=count))
qa=json.loads((W/'mac-full-arithmetic45-source01/qualification01.json').read_bytes());qs=json.loads((W/'mac-assertion-provider50-source01/qualification01.json').read_bytes())
coeff=json.loads(read(qa['coefficient_store']))['coefficients']; extra=json.loads(read(qs['extra_coefficients']))['coefficients'];coeff+=extra
adata=json.loads(zlib.decompress(read(qa['chunks'][0]['data'])));sdata=json.loads(zlib.decompress(read(qs['chunks'][0]['data'])))
def terms(x):return [[col,int(coeff[c])]for col,c in x]
rows=[];floor=adata['low']
for r in adata['recipes']:
 if r[1]==1:rows.append([terms(r[2]),[[floor,1]]]);floor+=1
 else:rows.extend([[terms(r[2]),[[floor+1,1]]],[terms(r[3]),[[floor,4],[floor+1,1]]]]);floor+=2
assert len(rows)==512
for i,r in enumerate(sdata['records'][25:90]):
 assert r['index']==177979+i and r['assertion']==25+i
 if i<64:assert r['constructor']=='squareLinear' and terms(r['x'])==terms(r['y'])==[[49+i,1]]
 else:assert r['constructor']=='linear' and r['right']==[1,31] and terms(r['x'])==[[49+k,2**k]for k in range(64)] and terms(r['y'])==[[34,1]]
q=json.loads((W/'mac-first-epoch-nonzero61-source04/qualification01.json').read_bytes());db=Path(q['db']);before=(db.stat().st_size,db.stat().st_mtime_ns)
c=sqlite3.connect('file:'+str(db)+'?mode=ro&immutable=1',uri=True);c.execute('PRAGMA cache_size=-8192')
for r in q['rows']:
 raw=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(r['index'],)).fetchone();assert raw is not None
 original=[json.loads(raw[0]),json.loads(raw[1])];assert original==r['original'] and json.loads(raw[2])==r['origin']
 outlined=[sorted([[200692 if col==0 else col,k]for col,k in lc])for lc in original];assert outlined==r['outlined']
 expected=rows[r['index']]if r['index']<262 else [terms(lc)for lc in sdata['records'][r['index']-177954]['actual']]
 assert outlined==expected
for r in q['nodes']:
 raw=c.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(r['source'],)).fetchone()
 assert raw and dict(source=r['source'],op=raw[0],left=[raw[1],raw[2]],right=[raw[3],raw[4]],kind=raw[5],terms=json.loads(raw[6]),certificate=json.loads(raw[7]))==r
c.close();assert before==(db.stat().st_size,db.stat().st_mtime_ns)
f=json.loads((P/'failures01.json').read_bytes())
for e in f['kernel']:
 r=json.loads(read(e['receipt']));assert r['status']=='failed'and r['exit']!=0 and r['cleanup']['clean']and e['formal_credit']==0
 for key in ['source','stdout','stderr']:read(e[key])
 assert r['source']==e['source']and r['stdout']==e['stdout']and r['stderr']==e['stderr']
for e in f['source_predecessors']:
 for r in e['files']:read(r)
 assert e['fresh_kernel_credit']==0
out=dict(kind='Independent maintained generator replay and selected literal DATA/SQL/source association; no Lean invocation',stages=stages,epoch_range_rows=65,epoch_nonzero_rows=10,product_nodes=q['nodes'],pins_rehashed=len(checked),failed_kernel_attempts=2,failed_cleanup_clean=True,scope='Range hint construction changes49..112; zero/inverse seeding changes113/114. Legal guard and explicit constant/copy premises remain visible. No desired target satisfaction assumed by seeding; primitive-to-actual completeness separately requires constructed six-row arithmetic satisfaction. Canonical natural meaning and complete legal Transfer remain open.',full_transfer='OPEN')
(J/'source-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['epoch_range_rows','epoch_nonzero_rows','pins_rehashed','failed_kernel_attempts']}))
