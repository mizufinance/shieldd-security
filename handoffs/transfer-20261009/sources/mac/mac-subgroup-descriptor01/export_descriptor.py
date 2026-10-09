"""Transport the exact closed first subgroup slice; data only, no proof credit."""
import hashlib,json,sqlite3,sys,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent;ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-subgroup-descriptor01';CAPTURE=ROOT/'work/parent-full-program/capture'
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
nodes=[];assertions=[];references=set();rows=set()
for entry in db.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id BETWEEN 1 AND 58 ORDER BY id'):
    i,op,lk,li,rk,ri,kind,terms,cert=entry;cert=json.loads(cert)
    nodes.append(dict(source_node=i,operation=op,left=[lk,li],right=[rk,ri],
        expression=dict(kind=kind,terms=json.loads(terms)),certificate=cert))
    references.update([(lk,li),(rk,ri)]);rows.update(cert['rows'])
assert len(nodes)==58 and [n['source_node'] for n in nodes]==list(range(1,59))
for i,raw in db.execute('SELECT id,certificate FROM assertions WHERE id BETWEEN 1 AND 6 ORDER BY id'):
    cert=json.loads(raw);assertions.append(dict(source_assertion=i,certificate=cert))
    references.update(map(tuple,[cert['left'],cert['right']]));rows.update(cert['rows'])
assert len(assertions)==6
input_ids=sorted(i for kind,i in references if kind==1);assert input_ids==list(range(11,18))
assert all(1<=i<=58 for kind,i in references if kind==2),'external node cut port'
constants=[]
for i in sorted(i for kind,i in references if kind==0):
    value=db.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0]
    assert 0<=int(value,16)<MODULUS
    constants.append(dict(source_constant=i,canonical_scalar=value,integer=int(value,16)))
required_rows=sorted(rows);rows.add(200769);indexed=[]
for i in sorted(rows):
    a,b,origin=db.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone()
    def outline(value):return sorted([[200692 if col==0 and i!=200769 else col,v] for col,v in json.loads(value)])
    indexed.append(dict(capture_index=i,a=outline(a),b=outline(b),origin=json.loads(origin),
        unoutlined_a=json.loads(a),unoutlined_b=json.loads(b),
        attribution='source certificates' if i in required_rows else 'additional actual constant-copy link'))
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
descriptor=dict(schema='transfer-first-subgroup-source-certificate-transport-v1',runtime_sha=provenance['runtime_sha'],
    modulus=str(MODULUS),provenance_receipt_sha256=sha(provenance_path),qualified_inputs=provenance['inputs'],
    raw_program_identity=raw_identity,ordinary_relation_identity=relation,binary_receipt=framing,
    nodes=nodes,assertions=assertions,constants=constants,
    inputs=[dict(source_witness=i,compiler_column=3+i,terms=[[3+i,1]]) for i in input_ids],
    dependency_closure=dict(source_nodes=list(range(1,59)),source_assertions=list(range(1,7)),
        external_node_ports=[],actual_input_ids=input_ids,
        note='node operands reference13–17; assertions additionally introduce11–12'),
    selected_source_certificate_row_indices=required_rows,additional_boundary_row_indices=[200769],
    indexed_original_rows=indexed,constant_copy=200692,verifier_one_column=0,
    source_layout=dict(public=selection['source_identity']['source_public'],blocks=selection['source_identity']['source_blocks']),
    descriptor_scope='exact raw source/selected compiler certificate/indexed row data; subgroup semantics unproved',
    kernel_run=False,proof_credit=0,full_transfer='OPEN')
path=OUT/'subgroup01.json';assert not path.exists();path.write_text(json.dumps(descriptor,indent=2)+'\n')
receipt=dict(status='passed',descriptor_sha256=sha(path),descriptor_bytes=path.stat().st_size,
    source_nodes=58,source_assertions=6,source_constants=len(constants),source_inputs=input_ids,
    source_certificate_rows=len(required_rows),additional_copy_rows=1,raw_index_body_matches=len(matched),
    maximum_expression_terms=max(len(n['expression']['terms']) for n in nodes),
    seconds=time.monotonic()-started,source_sha256=sha(Path(__file__).resolve()),
    readers_sha256={entry['path']:entry['sha256'] for entry in helpers},kernel_run=False,proof_credit=0)
(OUT/'descriptor-result01.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
