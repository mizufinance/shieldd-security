"""Read-only independently derived finite cut data; no kernel/native credit."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode
import copy,hashlib,json,sqlite3,subprocess,time
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12';CAP=R/'work/parent-full-program/capture'
sys.pycache_prefix=str(S/'unused-cache');assert not Path(sys.pycache_prefix).exists()
sys.path.insert(0,str(R/'work/mac-m18-framing01/python'))
from circuits.transfer_source_program import inspect_stream
from circuits.transfer_relation import inspect as inspect_relation,MODULUS
from circuits.transfer_spool import SpoolJSONL,load_shape
from circuits.transfer_program_lowering import canonical

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
start=time.monotonic();prpath=R/'outputs/mac-transfer-pilot01/provenance-successor01.json';assert sha(prpath)=='0a4e785984023ff3ba4cf7ad9ce8d7668dd6f003311e6afd66d9d43dfdfb458b';pr=json.loads(prpath.read_bytes());before={n:sha(CAP/n) for n in pr['inputs']};assert all(before[n]==i['sha256'] for n,i in pr['inputs'].items())
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R/'work/runtime-snapshot',text=True).strip()==pr['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert not subprocess.check_output(['git','status','--porcelain'],cwd=R/'work/runtime-snapshot',text=True).strip()
reader=R/'outputs/mac-m18-framing01/input-manifest.json';readers=json.loads(reader.read_bytes())['sources'];readeridentity=sha(reader)
for x in readers:assert sha(R/'work/mac-m18-framing01'/x['path'])==x['sha256']
source_sha=sha(Path(__file__));db=sqlite3.connect((CAP/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16384');nodes=[];constants={}
for i in range(129139,129145):
 op,lk,li,rk,ri,kind,terms,cert=db.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(i,)).fetchone();n=dict(source_node=i,operation=op,left=[lk,li],right=[rk,ri],expression=dict(kind=kind,terms=json.loads(terms)),certificate=json.loads(cert));nodes.append(n)
 for k,j in [n['left'],n['right']]:
  if k==0:constants[j]=int(db.execute('SELECT value FROM constants WHERE id=?',(j,)).fetchone()[0],16)
byid={n['source_node']:n for n in nodes}
def terms(ref):
 k,i=ref
 if k==0:return [[0,constants[i]]] if constants[i] else []
 if k==1:assert i<22735;return [[3+i,1]]
 assert k==2 and i in byid;return byid[i]['expression']['terms']
rows={}
for i in [11058,11059,11060,11061,200769]:
 a,b,origin=db.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone();rows[i]=dict(capture_index=i,unoutlined_a=json.loads(a),unoutlined_b=json.loads(b),origin=json.loads(origin))
def check(candidate_nodes,candidate_constants,candidate_rows):
 def term(ref):
  k,i=ref
  if k==0:return [[0,candidate_constants[i]]] if candidate_constants[i] else []
  if k==1:return [[3+i,1]]
  return candidate_nodes[i]['expression']['terms']
 writes=[];allocated=[];covered=[]
 for i,n in sorted(candidate_nodes.items()):
  c=n['certificate'];assert c['node']==i and c['left']==n['left'] and c['right']==n['right'];assert n['expression']['kind']=='linear'
  for k,j in [n['left'],n['right']]:assert k in [0,1,2] and (k!=2 or j<i and j in candidate_nodes)
  x,y=term(n['left']),term(n['right'])
  if n['operation']=='add':
   assert c['constructor']=='add' and c['rows']==[];assert tuple(map(tuple,n['expression']['terms']))==canonical(x+y)
  else:
   assert n['operation']=='mul' and c['constructor']=='product' and len(c['rows'])==2
   z=n['expression']['terms'];aux=c['auxiliary'];assert len(z)==len(aux)==1 and z[0][1]==aux[0][1]==1 and z[0][0]!=aux[0][0];writes.extend([z[0][0],aux[0][0]]);allocated.append(i);covered.extend(c['rows'])
   minus,plus=[candidate_rows[j] for j in c['rows']]
   for actual,expected in [(minus['unoutlined_a'],x+[[col,-v] for col,v in y]),(minus['unoutlined_b'],aux),(plus['unoutlined_a'],x+y),(plus['unoutlined_b'],aux+[[col,4*v] for col,v in z])]:assert tuple(map(tuple,actual))==canonical(expected)
 assert writes==[33796,33797,33798,33799] and allocated==[129140,129143] and covered==[11058,11059,11060,11061]
 assert set(candidate_constants)=={73390,73391,73392,73393}
 return dict(writes=writes,materialized_steps=len(allocated),arithmetic_rows=len(covered),source_inputs=sorted({j for n in candidate_nodes.values() for k,j in [n['left'],n['right']] if k==1}))
summary=check(byid,constants,rows);assert summary['source_inputs']==[7,20,21]
seen_nodes=set();seen_constants=set()
def graph(rec):
 if rec.get('node') in byid:
  n=byid[rec['node']];assert rec==dict(node=n['source_node'],operation=n['operation'],left=n['left'],right=n['right']);seen_nodes.add(n['source_node'])
 if rec.get('constant') in constants:assert int(rec['value'],16)==constants[rec['constant']];seen_constants.add(rec['constant'])
with (CAP/'program01.program.jsonl').open('rb') as f:rawidentity=inspect_stream(f,graph)
assert seen_nodes==set(byid) and seen_constants==set(constants)
seen_rows=set()
def ordinary(rec):
 i=rec['row']
 if i not in rows:return
 for side in ['a','b']:
  body=[[col,int(v,16)] for col,v in rec[side]];assert tuple(map(tuple,body))==canonical((200692 if col==0 and i!=200769 else col,v) for col,v in rows[i]['unoutlined_'+side]);rows[i][side]=body
 seen_rows.add(i)
with (CAP/'ordinary01.shape.json').open('rb') as f:shape=load_shape(f)
with (CAP/'ordinary01.rows').open('rb') as f:adapter=SpoolJSONL(f,shape,ordinary);relation=inspect_relation(adapter);framing=adapter.receipt()
assert seen_rows==set(rows) and framing==pr['adapter']
# Fixed source grammar derived independently, then compared to the inherited cut LCs.
upstream=R/'outputs/mac-poseidon-width6-upstream11/portable-input01.json';assert sha(upstream)=='74189456aa7380c35040e1c67d3b9d3ad48ce75d332ac80ad44971f1c0812ab9';u=json.loads(upstream.read_bytes());assert byid[129141]['expression']['terms']==u['input_terms'][7] and byid[129144]['expression']['terms']==u['input_terms'][8]
controls=[]
for mutation in ['operation','dependency','constant','coefficient','missing_row']:
 ns=copy.deepcopy(byid);cs=constants.copy();rs=copy.deepcopy(rows)
 if mutation=='operation':ns[129139]['operation']='mul'
 if mutation=='dependency':ns[129140]['right']=[1,21]
 if mutation=='constant':cs[73390]+=1
 if mutation=='coefficient':rs[11059]['unoutlined_b'][0][1]+=1
 if mutation=='missing_row':del rs[11061]
 try:check(ns,cs,rs)
 except (AssertionError,KeyError):controls.append(dict(mutation=mutation,rejected=True,scope='DATA same qualifier'))
 else:raise RuntimeError('Mutation accepted: '+mutation)
assert {n:sha(CAP/n) for n in before}==before and sha(Path(__file__))==source_sha and sha(reader)==readeridentity
for x in readers:assert sha(R/'work/mac-m18-framing01'/x['path'])==x['sha256']
assert not Path(sys.pycache_prefix).exists()
descriptor=dict(schema='qualified-two-product-cut12-v1',runtime_sha=pr['runtime_sha'],modulus=str(MODULUS),nodes=nodes,constants=[dict(id=i,value=v) for i,v in sorted(constants.items())],indexed_original_rows=[rows[i] for i in sorted(rows)],source_inputs=summary['source_inputs'],source_input_columns=[3+i for i in summary['source_inputs']],write_columns=summary['writes'],materialized_steps=summary['materialized_steps'],copy_row=200769,copy_column=200692,qualified_inputs=pr['inputs'],qualified_reader_sources=readers,reader_manifest_sha256=readeridentity,source_guard=dict(path=str(Path(__file__).relative_to(R)),sha256=source_sha),provenance_receipt_sha256=sha(prpath),raw_program_identity=rawidentity,ordinary_relation_identity=relation,binary_receipt=framing,inherited_upstream_input_sha256=sha(upstream),controls=controls,kernel_runs=0,full_transfer='OPEN')
p=O/'cut01.json';assert not p.exists();p.write_text(json.dumps(descriptor,indent=2)+'\n');result=dict(status='passed',descriptor_sha256=sha(p),descriptor_bytes=p.stat().st_size,nodes=6,constants=4,arithmetic_rows=4,selected_rows=5,materialized_steps=2,steps_with_copy=3,proposed_joined_steps=867,proposed_joined_rows=1157,writes=summary['writes'],controls=len(controls),seconds=time.monotonic()-start,kernel_runs=0,proof_credit=0);(O/'qualification-result01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
