"""Finite exact second-tail qualification. Raw source/RowSpool correspondence remains data evidence."""
import hashlib,json,sqlite3,sys,time
from pathlib import Path
if not __debug__:raise RuntimeError('optimized mode forbidden')
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-rename05';CAP=R/'work/parent-full-program/capture'
sys.path.insert(0,str(R/'work/mac-m18-framing01/python'));sys.path.insert(0,str(R/'work/mac-poseidon-call04'))
from circuits.transfer_source_program import inspect_stream
from circuits.transfer_relation import inspect as inspect_relation,MODULUS
from circuits.transfer_spool import SpoolJSONL,load_shape
from circuits.transfer_program_lowering import canonical
from validate_records import validate_node
start=time.monotonic()
reader_manifest=R/'outputs/mac-m18-framing01/input-manifest.json'
reader_manifest_sha=hashlib.sha256(reader_manifest.read_bytes()).hexdigest()
reader_sources=json.loads(reader_manifest.read_text())['sources']
def reader_sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for item in reader_sources:assert reader_sha(R/'work/mac-m18-framing01'/item['path'])==item['sha256']

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
p=json.loads((R/'outputs/mac-transfer-pilot01/provenance-successor01.json').read_text());inputs={n:sha(CAP/n) for n in p['inputs']};assert all(inputs[n]==v['sha256'] for n,v in p['inputs'].items())
paths=[R/'work/parent-poseidon-census01/result03.json',R/'work/parent-poseidon-renaming01/check.py',R/'work/parent-poseidon-renaming01/result.json',R/'work/mac-poseidon-call04/validate_records.py',Path(__file__)]
identities={str(q.relative_to(R)):sha(q) for q in paths};census=json.loads(paths[0].read_text());assert census['database_sha256']==inputs['lowering-resume01.sqlite'];parent=json.loads(paths[2].read_text());assert parent['census_sha256']==sha(paths[0])
a=next(x for x in census['matches'] if x['width']==6 and x['nodes']==[577,5865]);b=next(x for x in census['matches'] if x['width']==6 and x['nodes']==[5951,11239]);reference=[x for x in a['round_ports'] if x['round']>=2];target=[x for x in b['round_ports'] if x['round']>=2];assert len(reference)==len(target)==63
record=next(x for x in parent['matched'] if x['width']==6 and x['source_span']==b['nodes']);assert record['column_offset_from_reference']==416 and record['row_count']==372
conn=sqlite3.connect((CAP/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True);conn.execute('PRAGMA cache_size=-16384')
copy=200692;offset=416;nodeOffset=5374;constantOffset=3118
rename=lambda col: col+offset if 23060<=col<23472 else col-offset if 23476<=col<23888 else col
lc=lambda terms:[[rename(col),coef] for col,coef in terms]
nodes={};constants={};rows={};rounds=[]
def node(i):
 op,lk,li,rk,ri,kind,terms,cert=conn.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(i,)).fetchone();v=dict(source_node=i,operation=op,left=[lk,li],right=[rk,ri],expression=dict(kind=kind,terms=json.loads(terms)),certificate=json.loads(cert));validate_node(v);return v
for source,dest in zip(reference,target):
 assert source['round']==dest['round'] and [i+nodeOffset for i in source['nodes']]==dest['nodes']
 indices=set();sourceIndices=set()
 for i in range(source['nodes'][0],source['nodes'][1]+1):
  first=node(i);second=node(i+nodeOffset);nodes[second['source_node']]=second
  assert first['operation']==second['operation'] and first['expression']['kind']==second['expression']['kind'] and lc(first['expression']['terms'])==second['expression']['terms']
  def port(ref):
   kind,index=ref
   if kind==2:return [kind,index+nodeOffset]
   assert kind==0
   value=conn.execute('SELECT value FROM constants WHERE id=?',(index,)).fetchone()[0];actual=conn.execute('SELECT value FROM constants WHERE id=?',(index+constantOffset,)).fetchone()[0];assert value==actual;constants[index+constantOffset]=actual;return [kind,index+constantOffset]
  assert port(first['left'])==second['left'] and port(first['right'])==second['right']
  cert=dict(first['certificate']);assert set(cert)<=set(['node','left','right','rows','constructor','auxiliary','coefficient'])
  cert['node']+=nodeOffset;cert['left']=port(cert['left']);cert['right']=port(cert['right']);cert['rows']=[j+offset for j in cert['rows']]
  if 'auxiliary' in cert:cert['auxiliary']=lc(cert['auxiliary'])
  assert cert==second['certificate'];indices.update(cert['rows']);sourceIndices.update(first['certificate']['rows'])
  if cert['constructor'].startswith('folded'):assert cert['coefficient']==int(constants[cert['left'][1] if cert['constructor']=='foldedLeft' else cert['right'][1]],16)
 for i,j in zip(sorted(sourceIndices),sorted(indices)):
  assert i+offset==j
  aa,ab=conn.execute('SELECT a,b FROM rows WHERE id=?',(i,)).fetchone();ba,bb,origin=conn.execute('SELECT a,b,origin FROM rows WHERE id=?',(j,)).fetchone();assert lc(json.loads(aa))==json.loads(ba) and lc(json.loads(ab))==json.loads(bb)
  assert j not in rows;rows[j]=dict(capture_index=j,source_reference_index=i,unoutlined_a=json.loads(ba),unoutlined_b=json.loads(bb),origin=json.loads(origin))
 entry=dict(round=source['round'],source_nodes=dest['nodes'],row_indices=sorted(indices),source_reference_indices=sorted(sourceIndices))
 for label in ['before','after']:
  assert [[2,ref[1]+nodeOffset] for ref in source[label]]==dest[label]
  terms=[json.loads(conn.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0]) for ref in dest[label]]
  old=[json.loads(conn.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0]) for ref in source[label]];assert [lc(t) for t in old]==terms;entry[label]=terms;entry[label+'_raw_ports']=dest[label]
 rounds.append(entry)
assert sorted(rows)==list(range(778,1150));a,b,origin=conn.execute('SELECT a,b,origin FROM rows WHERE id=200769').fetchone();rows[200769]=dict(capture_index=200769,source_reference_index=200769,unoutlined_a=json.loads(a),unoutlined_b=json.loads(b),origin=json.loads(origin))
seenNodes=set();seenConstants=set()
def graph(record):
 if record.get('node') in nodes:
  n=nodes[record['node']];assert record==dict(node=n['source_node'],operation=n['operation'],left=n['left'],right=n['right']);seenNodes.add(n['source_node'])
 if record.get('constant') in constants:assert record['value']==constants[record['constant']];seenConstants.add(record['constant'])
with (CAP/'program01.program.jsonl').open('rb') as f:rawIdentity=inspect_stream(f,graph)
assert seenNodes==set(nodes) and seenConstants==set(constants)
seenRows=set()
def rawrow(record):
 i=record['row']
 if i not in rows:return
 value=rows[i]
 for side in ['a','b']:
  actual=[[col,int(v,16)] for col,v in record[side]];expected=canonical((copy if col==0 and i!=200769 else col,coef) for col,coef in value['unoutlined_'+side]);assert tuple(map(tuple,actual))==expected;value[side]=actual
 seenRows.add(i)
with (CAP/'ordinary01.shape.json').open('rb') as f:shape=load_shape(f)
with (CAP/'ordinary01.rows').open('rb') as f:adapter=SpoolJSONL(f,shape,rawrow);relation=inspect_relation(adapter);framing=adapter.receipt()
assert seenRows==set(rows) and framing==p['adapter']
for item in reader_sources:assert reader_sha(R/'work/mac-m18-framing01'/item['path'])==item['sha256']
assert reader_sha(reader_manifest)==reader_manifest_sha
assert {n:sha(CAP/n) for n in inputs}==inputs and {str(q.relative_to(R)):sha(q) for q in paths}==identities
packet=dict(qualified_reader_manifest_sha256=reader_manifest_sha,qualified_reader_sources=reader_sources,schema='exact-second-width6-tail-v1',runtime_sha=p['runtime_sha'],modulus=str(MODULUS),source_guards=identities,qualified_inputs=p['inputs'],provenance_receipt_sha256=sha(R/'outputs/mac-transfer-pilot01/provenance-successor01.json'),source_template_manifest_sha256='5bab86f7273095c37c570e3d148c8e93a01f1c61aa6cd40c89c1916bd5a80139',window=dict(start=23060,width=412,offset=416,copy=copy,fixed_original_upper=22738),source_nodes=[6047,11239],rounds=rounds,indexed_original_rows=[rows[i] for i in sorted(rows)],node_pairs=len(nodes),matched_constants=len(constants),raw_program_identity=rawIdentity,ordinary_relation_identity=relation,binary_receipt=framing,operation_pairs_digest=hashlib.sha256(json.dumps(nodes,sort_keys=True,separators=(',',':')).encode()).hexdigest(),raw_source_mapping_credit='qualified data only',full_transfer='OPEN')
output=O/'second-tail02.json';assert not output.exists();output.write_text(json.dumps(packet,indent=2)+'\n');result=dict(status='passed',descriptor_sha256=sha(output),descriptor_bytes=output.stat().st_size,nodes=len(nodes),constants=len(constants),rows=len(rows),seconds=time.monotonic()-start,kernel_run=False,proof_credit=0);(O/'selection-result02.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
