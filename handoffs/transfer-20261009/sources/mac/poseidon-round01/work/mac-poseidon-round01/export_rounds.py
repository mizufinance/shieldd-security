"""Qualified finite round transport; no kernel or native-refinement credit."""
import hashlib,json,sqlite3,subprocess,sys,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent;ROOT=STAGE.parents[1];OUT=ROOT/'outputs/mac-poseidon-round01';CAP=ROOT/'work/parent-full-program/capture'
sys.path.insert(0,str(ROOT/'work/mac-m18-framing01/python'))
from circuits.transfer_source_program import inspect_stream
from circuits.transfer_relation import inspect as inspect_relation,MODULUS
from circuits.transfer_spool import SpoolJSONL,load_shape
from circuits.transfer_program_lowering import canonical
from validate_records import validate_node
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
guardFiles=[STAGE/name for name in ['export_rounds.py','validate_records.py','parent-match.py','parent-descriptor.json']]
guardIdentity={str(path.relative_to(ROOT)):sha(path) for path in guardFiles}
started=time.monotonic();p=json.loads((ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json').read_text())
parent_inputs=json.loads((OUT/'parent-inputs01.json').read_text())
for item in parent_inputs.values():assert sha(ROOT/item['path'])==item['sha256']
match=json.loads((STAGE/'parent-descriptor.json').read_text());assert match['runtime_sha']==p['runtime_sha']
assert sha(CAP/'lowering-resume01.sqlite')==p['inputs']['lowering-resume01.sqlite']['sha256']
parameter=ROOT/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json'
assert sha(parameter)==match['parameter_sha256']=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8'
assert sha(ROOT/'work/parent-full-program/runtime/crates/crypto/primitives/params/poseidon381-wide.json')==sha(parameter)
params=json.loads(parameter.read_text());assert int(params['modulus'])==MODULUS
fresh=OUT/'reproduced-parent-match03.json';assert not fresh.exists()
subprocess.run([sys.executable,str(STAGE/'parent-match.py'),'--database',str(CAP/'lowering-resume01.sqlite'),'--runtime',str(ROOT/'work/runtime-snapshot'),'--output',str(fresh)],check=True,stdout=subprocess.DEVNULL)
assert json.loads(fresh.read_text())==match
helpers=json.loads((ROOT/'outputs/mac-m18-framing01/input-manifest.json').read_text())['sources']
for helper in helpers:assert sha(ROOT/'work/mac-m18-framing01'/helper['path'])==helper['sha256']
db=sqlite3.connect((CAP/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True)
selection=json.loads(db.execute('SELECT value FROM metadata WHERE key="complete"').fetchone()[0]);copy=selection['constant_copy']
scopes=[];allnodes={};allconstants={};allrows={};cutports={}
for ordinal,lower in [(0,503),(1,577),(4,865)]:
 round=match['rounds'][ordinal];upper=round['nodes_inclusive'][1];assert round['nodes_inclusive'][0]==(507 if ordinal==0 else lower)
 nodes=[];references=set();indices=set()
 for i,op,lk,li,rk,ri,kind,terms,cert in db.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id BETWEEN ? AND ? ORDER BY id',(lower,upper)):
  c=json.loads(cert);n=dict(source_node=i,operation=op,left=[lk,li],right=[rk,ri],expression=dict(kind=kind,terms=json.loads(terms)),certificate=c)
  validate_node(n)
  if c['constructor'] in ['foldedLeft','foldedRight']:
   port=n['left'] if c['constructor']=='foldedLeft' else n['right']
   constant=int(db.execute('SELECT value FROM constants WHERE id=?',(port[1],)).fetchone()[0],16)
   assert c['coefficient']==constant
  nodes.append(n);allnodes[i]=n;references.update([(lk,li),(rk,ri)]);indices.update(c['rows'])
 assert len(nodes)==upper-lower+1
 constants=[];external=[];inputs=[]
 for kind,i in sorted(references):
  if kind==0:
   value=db.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0]
   c=dict(source_constant=i,canonical_scalar=value,integer=int(value,16));constants.append(c);allconstants[i]=c
  elif kind==1:inputs.append(dict(source_witness=i,compiler_column=3+i,terms=[[3+i,1]]))
  elif not lower<=i<=upper:
   kind,terms=db.execute('SELECT kind,terms FROM nodes WHERE id=?',(i,)).fetchone()
   port=dict(source_node=i,expression=dict(kind=kind,terms=json.loads(terms)),role='prior state cut; upstream graph evaluation and compiler correspondence still open')
   external.append(port);cutports[i]=port
 if ordinal==0:assert inputs==[dict(source_witness=i,compiler_column=3+i,terms=[[3+i,1]]) for i in [11,12,18,19]] and not external
 else:assert not inputs and [x['source_node'] for x in external]==sorted(ref[1] for ref in round['before'])
 indices.add(selection['stored_rows']-1)
 for i in indices:
  a,b,origin=db.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone()
  allrows[i]=dict(capture_index=i,unoutlined_a=json.loads(a),unoutlined_b=json.loads(b),origin=json.loads(origin))
 counts={}
 for n in nodes:ctor=n['certificate']['constructor'];counts[ctor]=counts.get(ctor,0)+1
 scopes.append(dict(round=ordinal,full=ordinal<4,source_nodes_inclusive=[lower,upper],arithmetic_nodes=len(nodes),
  nodes=nodes,constants=constants,input_leaves=inputs,external_ports=external,phase_ports=round,
  arithmetic_row_indices=sorted(indices-{selection['stored_rows']-1}),rows_with_actual_copy_link=sorted(indices),
  constructors=counts,max_observed_node_terms=max(len(n['expression']['terms']) for n in nodes),
  scope='round0 includes absorption and native state0/state5 folding; later rounds have six explicit prior-state cut ports'))
# Compare operation/operand IDs and every referenced constant against raw graph stream.
seenNodes=set();seenConstants=set();seenCuts=set()
def raw_graph(record):
 if record.get('node') in allnodes:
  i=record['node'];n=allnodes[i];assert record==dict(node=i,operation=n['operation'],left=n['left'],right=n['right']);seenNodes.add(i)
 if record.get('node') in cutports:seenCuts.add(record['node'])
 if record.get('constant') in allconstants:
  i=record['constant'];assert record['value']==allconstants[i]['canonical_scalar'];seenConstants.add(i)
with (CAP/'program01.program.jsonl').open('rb') as f:rawIdentity=inspect_stream(f,raw_graph)
assert rawIdentity==selection['source_identity'] and seenNodes==set(allnodes) and seenConstants==set(allconstants) and seenCuts==set(cutports)
seenRows=set()
def raw_row(record):
 i=record['row']
 if i not in allrows:return
 r=allrows[i]
 for side in ['a','b']:
  actual=[[col,int(v,16)] for col,v in record[side]]
  expected=canonical((copy if col==0 and i!=selection['stored_rows']-1 else col,coef) for col,coef in r['unoutlined_'+side])
  assert tuple(map(tuple,actual))==expected,(i,side)
  r[side]=actual
 seenRows.add(i)
with (CAP/'ordinary01.shape.json').open('rb') as f:shape=load_shape(f)
with (CAP/'ordinary01.rows').open('rb') as f:
 adapter=SpoolJSONL(f,shape,raw_row);relation=inspect_relation(adapter);framing=adapter.receipt()
assert seenRows==set(allrows) and framing==p['adapter']
for helper in helpers:assert sha(ROOT/'work/mac-m18-framing01'/helper['path'])==helper['sha256']
assert sha(CAP/'lowering-resume01.sqlite')==p['inputs']['lowering-resume01.sqlite']['sha256']
assert sha(parameter)==match['parameter_sha256']
for item in parent_inputs.values():assert sha(ROOT/item['path'])==item['sha256']
assert guardIdentity=={str(path.relative_to(ROOT)):sha(path) for path in guardFiles}
result=dict(source_guard_identities=guardIdentity,schema='actual-poseidon-bounded-rounds-v1',runtime_sha=p['runtime_sha'],modulus=str(MODULUS),qualified_inputs=p['inputs'],
 provenance_receipt_sha256=sha(ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'),qualified_reader_sources=helpers,
 parent_inputs=parent_inputs,parameter_sha256=sha(parameter),parameters=params,raw_program_identity=rawIdentity,
 ordinary_relation_identity=relation,binary_receipt=framing,constant_copy=copy,actual_copy_row_index=selection['stored_rows']-1,
 selected_rounds=scopes,indexed_original_rows=[allrows[i] for i in sorted(allrows)],
 kernel_run=False,proof_credit=0,native_round_semantics='OPEN',cut_context_composition='OPEN',full_transfer='OPEN')
pth=OUT/'rounds03.json';assert not pth.exists();pth.write_text(json.dumps(result,indent=2)+'\n')
receipt=dict(status='passed',descriptor_sha256=sha(pth),descriptor_bytes=pth.stat().st_size,selected_nodes=len(allnodes),selected_constants=len(allconstants),indexed_rows=len(allrows),cut_ports=len(cutports),
 scopes=[{k:v for k,v in x.items() if k not in ['nodes','constants','phase_ports','input_leaves','external_ports']} for x in scopes],seconds=time.monotonic()-started,kernel_run=False,proof_credit=0,full_transfer='OPEN')
(OUT/'descriptor-result03.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
