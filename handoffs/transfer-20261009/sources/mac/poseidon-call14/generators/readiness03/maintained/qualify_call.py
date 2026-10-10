"""Independent finite upstream qualification; no kernel/native proof credit."""
import argparse,copy,hashlib,json,sqlite3,sys,time,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python unsupported')
S=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);parser.add_argument('--output-dir',type=Path,required=True);args=parser.parse_args();R=args.root.resolve();O=args.output_dir.resolve();CAP=R/'work/parent-full-program/capture';assert O.is_dir()
assert sys.flags.isolated and sys.flags.dont_write_bytecode
sys.pycache_prefix=str(S/'unused-cache');assert not Path(sys.pycache_prefix).exists()
sys.path.insert(0,str(S))
sys.path.insert(0,str(R/'work/mac-m18-framing01/python'))
from circuits.transfer_source_program import inspect_stream
from circuits.transfer_relation import inspect as inspect_relation,MODULUS
from circuits.transfer_spool import SpoolJSONL,load_shape
from circuits.transfer_program_lowering import canonical
from validate_records import validate_node
from source_match import match
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
start=time.monotonic();provenance=R/'outputs/mac-transfer-pilot01/provenance-successor01.json';pr=json.loads(provenance.read_text());inputs={n:sha(CAP/n) for n in pr['inputs']};assert all(inputs[n]==v['sha256'] for n,v in pr['inputs'].items())

assert sha(provenance)=='0a4e785984023ff3ba4cf7ad9ce8d7668dd6f003311e6afd66d9d43dfdfb458b'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R/'work/runtime-snapshot',text=True).strip()==pr['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=R/'work/runtime-snapshot',text=True).strip()
census_path=R/'work/parent-poseidon-call-census01/qualified01.json';assert sha(census_path)=='dc29cc844db6ffc0f37a99e5e3495f7d16f2ae2b3bfd8c3f065280c1cdc5d99b'
candidate=json.loads(census_path.read_text())['calls'][1]
assert (candidate['width'],candidate['domain'],candidate['arity'],candidate['IV'])==(6,24,6,1560)

reader=R/'outputs/mac-m18-framing01/input-manifest.json';reader_sha=sha(reader);readers=json.loads(reader.read_text())['sources']
for item in readers:assert sha(R/'work/mac-m18-framing01'/item['path'])==item['sha256']
parameter=R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json';parameter_sha=sha(parameter);assert parameter_sha=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8';params=json.loads(parameter.read_text());assert sha(R/'work/parent-full-program/runtime/crates/crypto/primitives/params/poseidon381-wide.json')==parameter_sha
ark=[[int(v,16) for v in row] for row in params['ark']];mds=[[int(v,16) for v in row] for row in params['mds']]
guards={str(f.relative_to(R)):sha(f) for f in [Path(__file__),S/'source_match.py',S/'validate_records.py',parameter]}
db=sqlite3.connect((CAP/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16384')
nodes={};records={};constants={};rows={}
def load_node(i):
 op,lk,li,rk,ri,kind,terms,cert=db.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(i,)).fetchone()
 n=dict(source_node=i,operation=op,left=[lk,li],right=[rk,ri],expression=dict(kind=kind,terms=json.loads(terms)),certificate=json.loads(cert));validate_node(n)
 for port in [n['left'],n['right']]:
  if port[0]==0:constants[port[1]]=int(db.execute('SELECT value FROM constants WHERE id=?',(port[1],)).fetchone()[0],16)
 return n
for i in range(5866,16626):
 n=load_node(i);nodes[i]=n;records[i]=(n['operation'],*n['left'],*n['right'])
expected_inputs=[(1,20),(1,21),(1,27),(1,28),(1,29),(1,30)]
matched=match(records,constants,ark,mds,expected_inputs,24,6,5866)
assert matched['result']==(2,16577) and matched['blocks'][0]['absorption_nodes']==[5866,5870] and matched['blocks'][1]['absorption_nodes']==[11240,11240] and len(matched['blocks'])==2
def terms(ref):
 kind,i=ref
 if kind=='native':return [[0,i]] if i else []
 if kind==0:return [[0,constants[i]]] if constants[i] else []
 if kind==1:return [[3+i,1]]
 assert kind==2
 return nodes[i]['expression']['terms'] if i in nodes else json.loads(db.execute('SELECT terms FROM nodes WHERE id=?',(i,)).fetchone()[0])
def read_row(i):
 a,b,origin=db.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone();return dict(capture_index=i,unoutlined_a=json.loads(a),unoutlined_b=json.loads(b),origin=json.loads(origin))
summary_blocks=[];prefix_scopes=[]
for block in matched['blocks']:
 indices=sorted({i for n in nodes.values() if block['absorption_nodes'][0]<=n['source_node']<=block['rounds'][-1]['nodes'][1] for i in n['certificate']['rows']})
 assert indices==list(range(indices[0],indices[-1]+1));writes=sorted({c for n in nodes.values() if block['absorption_nodes'][0]<=n['source_node']<=block['rounds'][-1]['nodes'][1] and n['certificate']['constructor'] in ['square','product'] for c,v in n['expression']['terms']+n['certificate'].get('auxiliary',[])})
 assert writes==list(range(writes[0],writes[-1]+1));rows.update({i:read_row(i) for i in indices})
 phases=[]
 for round_ in block['rounds']:
  phase=dict(round=round_['round'],nodes=round_['nodes'],ports={label:[terms(ref) for ref in round_[label]] for label in ['before','after_ark','after_sbox','after']},raw_ports={label:round_[label] for label in ['before','after_ark','after_sbox','after']},row_indices=sorted({i for j in range(round_['nodes'][0],round_['nodes'][1]+1) for i in nodes[j]['certificate']['rows']}))
  phases.append(phase)
  if round_['round']<=1:
   first=block['absorption_nodes'][0] if round_['round']==0 else round_['nodes'][0]
   prefix_scopes.append(dict(block=block['block'],round=round_['round'],nodes=[nodes[i] for i in range(first,round_['nodes'][1]+1)],phase=phase))
 summary_blocks.append(dict(block=block['block'],node_span=[block['absorption_nodes'][0],block['rounds'][-1]['nodes'][1]],absorption_nodes=block['absorption_nodes'],before_absorption=[terms(ref) for ref in block['before_absorption']],absorbed=[terms(ref) for ref in block['absorbed']],chunk=[terms(ref) for ref in block['chunk']],rounds=phases,row_indices=indices,writes=[writes[0],writes[-1]],materialized_steps=sum(n['certificate']['constructor'] in ['square','product'] for i,n in nodes.items() if block['absorption_nodes'][0]<=i<=block['rounds'][-1]['nodes'][1])))
# Verify full round2..64 row/port/certificate translation, not only digest equality.
translations=[]
for block in summary_blocks:
 target=block['rounds'][2:];reference=json.loads((R/'work/parent-poseidon-census01/result03.json').read_text())['matches'];reference=next(v for v in reference if v['width']==6 and v['nodes']==[577,5865])['round_ports'][1:];assert len(target)==len(reference)==63
 old_before=[json.loads(db.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0]) for ref in reference[0]['before']]
 offset=min(c for body in target[0]['ports']['before'] for c,v in body if c not in [0,200692])-min(c for body in old_before for c,v in body if c not in [0,200692])
 translate=lambda body:[[c+offset if 23060<=c<23472 else c,v] for c,v in body]
 source_indices=[];target_indices=[];node_shift=target[0]['nodes'][0]-reference[0]['nodes'][0];constant_shift=None
 for a,b in zip(reference,target):
  assert a['round']==b['round'] and [i+node_shift for i in a['nodes']]==b['nodes']
  for label in ['before','after']:
   old=[json.loads(db.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0]) for ref in a[label]];assert [translate(t) for t in old]==b['ports'][label]
  for i in range(a['nodes'][0],a['nodes'][1]+1):
   old=load_node(i);actual=nodes[i+node_shift];assert translate(old['expression']['terms'])==actual['expression']['terms'] and old['operation']==actual['operation']
   for x,y in zip([old['left'],old['right']],[actual['left'],actual['right']]):
    assert x[0]==y[0]
    if x[0]==2:assert x[1]+node_shift==y[1]
    else:
     assert x[0]==0 and constants[x[1]]==constants[y[1]]
     delta=y[1]-x[1];constant_shift=delta if constant_shift is None else constant_shift;assert delta==constant_shift
   source_indices.extend(old['certificate']['rows']);target_indices.extend(actual['certificate']['rows'])
 source_indices=sorted(set(source_indices));target_indices=sorted(set(target_indices));row_offset=target_indices[0]-source_indices[0];assert len(source_indices)==len(target_indices)==372
 for a,b in zip(reference,target):
  for i in range(a['nodes'][0],a['nodes'][1]+1):
   old=load_node(i);cert=dict(old['certificate']);cert['node']+=node_shift;cert['left']=[old['left'][0],old['left'][1]+(node_shift if old['left'][0]==2 else constant_shift)];cert['right']=[old['right'][0],old['right'][1]+(node_shift if old['right'][0]==2 else constant_shift)];cert['rows']=[j+row_offset for j in cert['rows']]
   if 'auxiliary' in cert:cert['auxiliary']=translate(cert['auxiliary'])
   assert cert==nodes[i+node_shift]['certificate'],('certificate',i)
 for a,b in zip(source_indices,target_indices):
  assert a+row_offset==b;old=read_row(a)
  for side in ['a','b']:assert translate(old['unoutlined_'+side])==rows[b]['unoutlined_'+side]
 translations.append(dict(block=block['block'],reference_window=[23060,23471],target_window=[23060+offset,23471+offset],column_offset=offset,row_offset=row_offset,node_offset=node_shift,constant_offset=constant_shift,tail_indices=target_indices,tail_rows=372,phase_pairs=63,reference_first_round_rows=source_indices[:24]))
# Independently reconstruct all compiler expression and actual emitted row equations.
for i,n in nodes.items():
 left=terms(n['left']);right=terms(n['right']);cert=n['certificate'];out=n['expression']['terms'];ctor=cert['constructor']
 assert n['expression']['kind']=='linear' and tuple(map(tuple,out))==canonical(out)
 if ctor=='add':assert tuple(map(tuple,out))==canonical(left+right)
 elif ctor in ['foldedLeft','foldedRight']:
  port=n['left'] if ctor=='foldedLeft' else n['right'];value=constants[port[1]];assert cert['coefficient']==value
  operand=right if ctor=='foldedLeft' else left;assert tuple(map(tuple,out))==canonical((col,v*value) for col,v in operand)
 elif ctor=='square':
  assert left==right and len(out)==1 and out[0][1]==1
  row=rows[cert['rows'][0]];assert row['unoutlined_a']==left and row['unoutlined_b']==out and row['origin']==dict(kind='node',id=i,role='square')
 elif ctor=='product':
  aux=cert['auxiliary'];assert left!=right and len(out)==len(aux)==1 and out[0][1]==aux[0][1]==1 and aux[0][0]==out[0][0]+1
  for index,a,b,role in [(cert['rows'][0],canonical(left+[[c,-v] for c,v in right]),canonical(aux),'minus'),(cert['rows'][1],canonical(left+right),canonical(aux+[[c,4*v] for c,v in out]),'plus')]:
   row=rows[index];assert tuple(map(tuple,row['unoutlined_a']))==a and tuple(map(tuple,row['unoutlined_b']))==b and row['origin']==dict(kind='node',id=i,role=role)
 else:raise ValueError('unexpected deferred constructor')
assert len(nodes)==10760 and sum(b['materialized_steps'] for b in summary_blocks)==627 and len(rows)==836
assert summary_blocks[0]['rounds'][-1]['ports']['after']==summary_blocks[1]['before_absorption']
assert summary_blocks[0]['before_absorption']==[[[0,1560]],[],[],[],[],[]]
assert summary_blocks[1]['absorbed'][0]==summary_blocks[1]['before_absorption'][0]
assert tuple(map(tuple,summary_blocks[1]['absorbed'][1]))==canonical(summary_blocks[1]['before_absorption'][1]+[[33,1]])
assert summary_blocks[1]['absorbed'][2:]==summary_blocks[1]['before_absorption'][2:]

rows[200769]=read_row(200769);seen_nodes=set();seen_constants=set();
# Use the matcher allocation list for exact allocated constant census.
actual_constants=dict(matched['matched_constants'])
def graph(rec):
 if rec.get('node') in nodes:
  n=nodes[rec['node']];assert rec==dict(node=n['source_node'],operation=n['operation'],left=n['left'],right=n['right']);seen_nodes.add(n['source_node'])
 if rec.get('constant') in actual_constants:assert int(rec['value'],16)==actual_constants[rec['constant']];seen_constants.add(rec['constant'])
with (CAP/'program01.program.jsonl').open('rb') as f:rawidentity=inspect_stream(f,graph)
assert seen_nodes==set(nodes) and seen_constants==set(actual_constants)
seen_rows=set()
def rawrow(rec):
 i=rec['row']
 if i not in rows:return
 for side in ['a','b']:
  body=[[c,int(v,16)] for c,v in rec[side]];assert tuple(map(tuple,body))==canonical((200692 if c==0 and i!=200769 else c,v) for c,v in rows[i]['unoutlined_'+side]);rows[i][side]=body
 seen_rows.add(i)
with (CAP/'ordinary01.shape.json').open('rb') as f:shape=load_shape(f)
with (CAP/'ordinary01.rows').open('rb') as f:adapter=SpoolJSONL(f,shape,rawrow);relation=inspect_relation(adapter);framing=adapter.receipt()
assert seen_rows==set(rows) and framing==pr['adapter']
controls=[]
variants=[];rs=records.copy();v=list(rs[5866]);v[0]='mul';rs[5866]=tuple(v);variants.append(('opcode',rs,actual_constants,ark,mds,expected_inputs,24,6))
cs=actual_constants.copy();cs[min(cs)]+=1;variants.append(('allocated_constant',records,cs,ark,mds,expected_inputs,24,6))
a=copy.deepcopy(ark);a[0][0]+=1;variants.append(('ARK0',records,actual_constants,a,mds,expected_inputs,24,6))
m=copy.deepcopy(mds);m[0][0]+=1;variants.append(('MDS',records,actual_constants,ark,m,expected_inputs,24,6))
ins=expected_inputs.copy();ins[0],ins[1]=ins[1],ins[0];variants.append(('input_order',records,actual_constants,ark,mds,ins,24,6))
variants.append(('domain',records,actual_constants,ark,mds,expected_inputs,25,6));variants.append(('arity',records,actual_constants,ark,mds,expected_inputs,24,7))
rs=records.copy();del rs[16625];variants.append(('missing_finalnode',rs,actual_constants,ark,mds,expected_inputs,24,6))
for name,rs,cs,a,m,ins,dom,arity in variants:
 try:match(rs,cs,a,m,ins,dom,arity,5866)
 except (AssertionError,KeyError) as error:controls.append(dict(mutation=name,rejected=True,reason=str(error)[:160]))
 else:raise RuntimeError('Mutation accepted: '+name)
assert {n:sha(CAP/n) for n in inputs}==inputs and all(sha(R/name)==h for name,h in guards.items()) and sha(reader)==reader_sha
output=O/'call1-qualification01.json';assert not output.exists();packet=dict(schema='qualified-width6-domain24-arity6-two-block-data-v1',runtime_sha=pr['runtime_sha'],modulus=str(MODULUS),qualified_inputs=pr['inputs'],qualified_reader_sources=readers,provenance_receipt_sha256=sha(provenance),source_guards=guards,parameter_sha256=parameter_sha,parameters=params,input_ports=expected_inputs,input_terms=[terms(ref) for ref in expected_inputs],blocks=summary_blocks,prefix_scopes=prefix_scopes,translations=translations,indexed_original_rows=[rows[i] for i in sorted(rows)],raw_program_identity=rawidentity,ordinary_relation_identity=relation,binary_receipt=framing,controls=controls,output=dict(raw16577_terms=terms((2,16577)),width3_call3_input0_equal=terms((2,16577))==json.loads((R/'outputs/mac-poseidon-width3-08/rounds01.json').read_text())['selected_rounds'][0]['external_ports'][0]['expression']['terms']),kernel_run=False,proof_credit=0,full_transfer='OPEN')

packet['census_sha256']=sha(census_path)
packet['census_candidate_index']=1
packet['accepted_child_round_input_sha256']=sha(R/'outputs/mac-poseidon-width3-08/rounds01.json')
packet['source_node_count']=len(nodes)
packet['allocated_constants']=[dict(id=i,value=v) for i,v in sorted(actual_constants.items())]
packet['actual_input_columns']=[3+ref[1] for ref in expected_inputs]
packet['final_state_raw']=matched['final_state']
packet['final_state_terms']=[terms(ref) for ref in matched['final_state']]
packet['materialized_steps']=sum(block['materialized_steps'] for block in summary_blocks)
packet['arithmetic_rows']=len(rows)-1
packet['max_internal_LC_terms']=max(len(n['expression']['terms']) for n in nodes.values())
packet['max_actual_row_LC_terms']=max(len(r[side]) for r in rows.values() for side in ['a','b'])
assert [list(ref) for ref in matched['final_state']]==candidate['final_state']
assert [list(ref) for ref in expected_inputs]==candidate['inputs']
for block in matched['blocks']:
 assert block['rounds'][0]['nodes']==candidate['permutations'][block['block']]['round0_span']
 assert block['rounds'][1]['nodes'][0]==candidate['permutations'][block['block']]['round1_64_span'][0]
 assert block['rounds'][-1]['nodes'][1]==candidate['permutations'][block['block']]['round1_64_span'][1]
assert not Path(sys.pycache_prefix).exists()

output.write_text(json.dumps(packet,indent=2)+'\n');result=dict(status='passed',descriptor_sha256=sha(output),descriptor_bytes=output.stat().st_size,nodes=len(nodes),constants=len(actual_constants),rows=len(rows),blocks=[dict(block=b['block'],nodes=b['node_span'],rows=len(b['row_indices']),indices=[b['row_indices'][0],b['row_indices'][-1]],writes=b['writes'],steps=b['materialized_steps']) for b in summary_blocks],translations=translations,controls=len(controls),seconds=time.monotonic()-start,kernel_run=False,proof_credit=0);(O/'qualification-result01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='translations'}))
