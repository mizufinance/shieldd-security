"""Transport the exact closed first subgroup slice; data only, no proof credit."""
import hashlib,json,sqlite3,sys,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent;ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-long-recipe01';CAPTURE=ROOT/'work/parent-full-program/capture'
sys.path.insert(0,str(ROOT/'work/mac-m18-framing01/python'))
from circuits.transfer_source_program import inspect_stream
from circuits.transfer_relation import inspect as inspect_relation,MODULUS
from circuits.transfer_spool import SpoolJSONL,load_shape
def sha(path):
    value=hashlib.sha256()
    with path.open('rb') as stream:
        while raw:=stream.read(1024**2):value.update(raw)
    return value.hexdigest()
started=time.monotonic()
provenance_path=ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'
provenance=json.loads(provenance_path.read_text())
assert sha(CAPTURE/'lowering-resume01.sqlite')==provenance['inputs']['lowering-resume01.sqlite']['sha256']
input_manifest=ROOT/'outputs/mac-m18-framing01/input-manifest.json'
helpers=json.loads(input_manifest.read_text())['sources']
for helper in helpers:assert sha(ROOT/'work/mac-m18-framing01'/helper['path'])==helper['sha256']
db=sqlite3.connect((CAPTURE/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True)
selection=json.loads(db.execute('SELECT value FROM metadata WHERE key="complete"').fetchone()[0])
assert selection['source_identity']==provenance['raw_graph_identity']
nodesById={}; references=set(); stack=[126788,126791]
while stack:
    i=stack.pop()
    if i in nodesById:continue
    entry=db.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(i,)).fetchone()
    i,op,lk,li,rk,ri,kind,terms,cert=entry;cert=json.loads(cert)
    assert cert['constructor'] in ['add','foldedLeft'] and kind=='linear'
    assert not cert['rows']
    nodesById[i]=dict(source_node=i,operation=op,left=[lk,li],right=[rk,ri],expression=dict(kind=kind,terms=json.loads(terms)),certificate=cert)
    for ref in [(lk,li),(rk,ri)]:
        references.add(ref)
        if ref[0]==2:stack.append(ref[1])
nodes=[nodesById[i] for i in sorted(nodesById)];assert len(nodes)==517
cert=json.loads(db.execute('SELECT certificate FROM assertions WHERE id=1202').fetchone()[0]);assert cert==dict(assertion=1202,left=[2,126788],right=[2,126791],constructor='linear',rows=[179156])
assertions=[dict(source_assertion=1202,certificate=cert)]
constants=[]
for i in sorted(i for k,i in references if k==0):
    value=db.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0]
    constants.append(dict(source_constant=i,canonical_scalar=value,integer=int(value,16)))
input_ids=sorted(i for k,i in references if k==1);assert len(input_ids)==258
assert len(constants)==261
assert all(i in nodesById for k,i in references if k==2)
a,b,origin=db.execute('SELECT a,b,origin FROM rows WHERE id=179156').fetchone()
a=json.loads(a);b=json.loads(b);assert len(a)==258 and not b and all(col not in [0,200692] for col,_ in a)
indexed=[dict(capture_index=179156,a=a,b=b,origin=json.loads(origin),unoutlined_a=a,unoutlined_b=b,attribution='source assertion1202')]
source_nodes={n['source_node']:n for n in nodes};source_assertions={a['source_assertion']:a for a in assertions}
source_constants={c['source_constant']:c for c in constants};seen=[set(),set(),set()]
def raw_source(record):
    if record.get('node') in source_nodes:
        i=record['node'];node=source_nodes[i]
        assert record==dict(node=i,operation=node['operation'],left=node['left'],right=node['right']);seen[0].add(i)
    if record.get('assertion') in source_assertions:
        i=record['assertion'];cert=source_assertions[i]['certificate']
        assert record==dict(assertion=i,left=cert['left'],right=cert['right']);seen[1].add(i)
    if record.get('constant') in source_constants:
        i=record['constant'];assert record['value']==source_constants[i]['canonical_scalar'];seen[2].add(i)
with (CAPTURE/'program01.program.jsonl').open('rb') as stream:raw_identity=inspect_stream(stream,raw_source)
assert raw_identity==selection['source_identity'] and seen==[set(source_nodes),set(source_assertions),set(source_constants)]
expected={r['capture_index']:r for r in indexed};matched=set()
def raw_row(record):
    i=record['row']
    if i in expected:
        for side in ['a','b']:assert [[col,int(value,16)] for col,value in record[side]]==expected[i][side]
        matched.add(i)
with (CAPTURE/'ordinary01.shape.json').open('rb') as stream:shape=load_shape(stream)
with (CAPTURE/'ordinary01.rows').open('rb') as stream:
    adapter=SpoolJSONL(stream,shape,raw_row);relation=inspect_relation(adapter);framing=adapter.receipt()
assert matched==set(expected) and framing==provenance['adapter']
for helper in helpers:assert sha(ROOT/'work/mac-m18-framing01'/helper['path'])==helper['sha256']
assert sha(CAPTURE/'lowering-resume01.sqlite')==provenance['inputs']['lowering-resume01.sqlite']['sha256']
descriptor=dict(schema='actual-long-add-scale-descriptor-v1',runtime_sha=provenance['runtime_sha'],modulus=str(MODULUS),provenance_receipt_sha256=sha(provenance_path),qualified_inputs=provenance['inputs'],raw_program_identity=raw_identity,ordinary_relation_identity=relation,binary_receipt=framing,nodes=nodes,assertions=assertions,constants=constants,inputs=[dict(source_witness=i,compiler_column=3+i,terms=[[3+i,1]]) for i in input_ids],indexed_original_rows=indexed,constant_copy=200692,dependency_closure=dict(source_nodes=sorted(nodesById),source_assertions=[1202],external_node_ports=[],actual_input_ids=input_ids),intermediate_lc_terms=sum(len(n['expression']['terms']) for n in nodes),consumer_terms=len(a),kernel_run=False,proof_credit=0,full_transfer='OPEN')
path=OUT/'long-chain01.json';assert not path.exists();path.write_text(json.dumps(descriptor,indent=2)+'\n')
receipt=dict(status='passed',descriptor_sha256=sha(path),descriptor_bytes=path.stat().st_size,raw_nodes=len(nodes),input_leaves=len(input_ids),constant_leaves=len(constants),consumer_terms=len(a),kernel_run=False,proof_credit=0,seconds=time.monotonic()-started)
(OUT/'descriptor-result01.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
