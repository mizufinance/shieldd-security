"""Finite cost/interface samples with typed cut operands; no full graph credit."""
import hashlib,json,sqlite3,sys,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-transfer-representative01'
CAPTURE=ROOT/'work/parent-full-program/capture'
sys.path.insert(0,str(ROOT/'work/mac-m18-framing01/python'))
from circuits.transfer_source_program import inspect_stream
from circuits.transfer_spool import SpoolJSONL,load_shape
from circuits.transfer_relation import inspect as inspect_relation,MODULUS
def sha(path):
    result=hashlib.sha256()
    with path.open('rb') as stream:
        while data:=stream.read(1024**2):result.update(data)
    return result.hexdigest()
started=time.monotonic()
provenance=json.loads((ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json').read_text())
assert sha(CAPTURE/'lowering-resume01.sqlite')==provenance['inputs']['lowering-resume01.sqlite']['sha256']
db=sqlite3.connect((CAPTURE/'lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True)
cases=[('First',0,0),('Middle',626442,11406),('High',1182800,22800),('Final',1252884,22812)]
nodes={};assertions={};constants={};selected_rows={};blocks=[]
def expression(reference):
    kind,index=reference
    if kind==0:
        value=int(db.execute('SELECT value FROM constants WHERE id=?',(index,)).fetchone()[0],16)
        constants[index]=value;return dict(kind='linear',terms=[[0,value]])
    if kind==1:return dict(kind='linear',terms=[[3+index,1]])
    found=db.execute('SELECT kind,terms FROM nodes WHERE id=?',(index,)).fetchone()
    return dict(kind=found[0],terms=json.loads(found[1]))
for label,start,assertion in cases:
    source=[]
    for row in db.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id>=? AND id<? ORDER BY id',(start,start+8)):
        index,op,lk,li,rk,ri,kind,terms,cert=row
        value=dict(id=index,op=op,left=[lk,li],right=[rk,ri],kind=kind,terms=json.loads(terms),certificate=json.loads(cert))
        value['left_expression']=expression(value['left']);value['right_expression']=expression(value['right'])
        nodes[index]=value;source.append(value)
    cert=json.loads(db.execute('SELECT certificate FROM assertions WHERE id=?',(assertion,)).fetchone()[0])
    assertions[assertion]=cert
    rows=sorted({i for n in source for i in n['certificate']['rows']}|set(cert['rows'])|{200769})
    arithmetic=sorted({i for n in source for i in n['certificate']['rows']}|{200769})
    for index in rows:
        a,b,origin=db.execute('SELECT a,b,origin FROM rows WHERE id=?',(index,)).fetchone()
        def outlined(raw):
            return sorted([[200692 if column==0 and index!=200769 else column,value]
                for column,value in json.loads(raw)])
        selected_rows[index]=dict(capture_index=index,a=outlined(a),b=outlined(b),origin=json.loads(origin))
    blocks.append(dict(label=label,nodes=source,assertion=cert,rows=rows,arithmetic_rows=arithmetic,
        assertion_left=expression(cert['left']),assertion_right=expression(cert['right'])))
seen_nodes=set();seen_constants=set();seen_assertions=set()
def record(item):
    if item.get('node') in nodes:
        n=nodes[item['node']];assert item==dict(node=n['id'],operation=n['op'],left=n['left'],right=n['right'])
        seen_nodes.add(n['id'])
    if item.get('constant') in constants:
        i=item['constant'];assert int(item['value'],16)==constants[i];seen_constants.add(i)
    if item.get('assertion') in assertions:
        i=item['assertion'];a=assertions[i];assert item==dict(assertion=i,left=a['left'],right=a['right']);seen_assertions.add(i)
with (CAPTURE/'program01.program.jsonl').open('rb') as stream:raw=inspect_stream(stream,record)
assert raw==provenance['raw_graph_identity'] and seen_nodes==set(nodes) and seen_constants==set(constants) and seen_assertions==set(assertions)
seen_rows=set()
def row(record):
    index=record['row']
    if index in selected_rows:
        for side in ['a','b']:assert [[col,int(value,16)] for col,value in record[side]]==selected_rows[index][side]
        seen_rows.add(index)
with (CAPTURE/'ordinary01.shape.json').open('rb') as stream:shape=load_shape(stream)
with (CAPTURE/'ordinary01.rows').open('rb') as stream:
    adapter=SpoolJSONL(stream,shape,row);relation=inspect_relation(adapter);framing=adapter.receipt()
assert seen_rows==set(selected_rows) and framing['binary_sha256']==provenance['adapter']['binary_sha256']
def literal(terms):return '['+', '.join(f'({c},{v})' for c,v in terms)+']'
summaries=[]
for block in blocks:
    label=block['label'];namespace='ShielddSecurity.TransferCost'+label+'01';pool={};declarations=[]
    def linear(terms):
        key=tuple(tuple(x) for x in terms)
        if key not in pool:
            name='lc'+str(len(pool));pool[key]=name;declarations.append('def '+name+' : Linear := '+literal(terms))
        return pool[key]
    def expr(e):return '.'+e['kind']+' '+linear(e['terms'])
    body=[];theorems=[];expected={};step_terms=[]
    for i,n in enumerate(block['nodes']):
        cert=n['certificate'];left=n['left_expression'];right=n['right_expression'];out=dict(kind=n['kind'],terms=n['terms'])
        x,y,z=linear(left['terms']),linear(right['terms']),linear(out['terms'])
        body += [f'def prior{i} (index : Fin 2) : Expression := if index.val = 0 then {expr(left)} else {expr(right)}',
            f'def operation{i} : SourceNode 2 := .{n["op"]} ⟨0,by decide⟩ ⟨1,by decide⟩',
            f'def output{i} : Expression := {expr(out)}']
        common=f'⟨0,by decide⟩ ⟨1,by decide⟩ {x} {y}'
        c=cert['constructor']
        if c=='add':proof=f'.add {common} {z} rfl rfl (by decide)'
        elif c.startswith('folded'):proof=f'.{c} {common} {z} {cert["coefficient"]} rfl rfl (by decide) (by decide)'
        elif c=='deferred':proof=f'.deferred {common} {z} rfl rfl (by decide) (by decide)'
        elif c=='square':
            proof=f'.square {common} {z} rfl rfl (by decide) (by decide)'
            assert len(n['terms'])==1 and n['terms'][0][1]==1
            step_terms.append(f'.square {x} [] {n["terms"][0][0]}')
            expected[cert['rows'][0]]=f'⟨{x},{z}⟩'
        elif c=='product':
            aux=linear(cert['auxiliary']);proof=f'.product {common} {z} {aux} rfl rfl (by decide) (by decide)'
            assert len(n['terms'])==len(cert['auxiliary'])==1 and n['terms'][0][1]==cert['auxiliary'][0][1]==1
            step_terms.append(f'.product {x} {y} [] {n["terms"][0][0]} {cert["auxiliary"][0][0]}')
            expected[cert['rows'][0]]=f'⟨Compiler.subtract {x} {y},{aux}⟩'
            expected[cert['rows'][1]]=f'⟨{x} ++ {y},{aux} ++ scaleLinear 4 {z}⟩'
        else:raise AssertionError(c)
        body += [f'theorem certificate{i} : NodeCertificate p unoutlined inputTerms prior{i} operation{i} output{i} := by',f'  exact {proof}']
        theorems.append(f'certificate{i}')
    a=block['assertion'];x=linear(block['assertion_left']['terms']);y=linear(block['assertion_right']['terms']);c=a['constructor']
    if c=='squares':
        aux=linear(a['auxiliary']);proof=f'.squares {x} {y} {aux} (by decide) (by decide)'
    else:proof=f'.{c} {x} {y} (by decide)'
    body += [f'theorem assertion_certificate : AssertionCertificate p unoutlined ({expr(block["assertion_left"])}) ({expr(block["assertion_right"])}) := by',f'  exact {proof}']
    theorems.append('assertion_certificate')
    row_names={}
    for index in block['rows']:
        r=selected_rows[index];name='captured'+str(index);row_names[index]=name
        declarations.append(f'def {name} : Row := ⟨{linear(r["a"])},{linear(r["b"])}⟩')
    declarations += ['def originalRows : List Row := ['+', '.join(row_names[i] for i in block['rows'])+']',
        'def unoutlined : List Row := unoutlineRows copy originalRows',
        'def indexedRows : Array (Nat × Row) := #['+', '.join(f'({i},{row_names[i]})' for i in block['rows'])+']',
        'def rowAt (index : Fin '+str(len(block['rows']))+") : Nat × Row := indexedRows[index.val]'(by simpa [indexedRows] using index.isLt)"]
    # An explicit indexed body map is over this local table only. Full relation
    # indexing/composition is intentionally not asserted by this cost sample.
    body += ['theorem rowAt_matches (index : Fin '+str(len(block['rows']))+') :',
        "    rowAt index = (indexedRows.toList[index.val]'(by simpa [indexedRows] using index.isLt)) := by",
        '  simp [rowAt]']
    theorems.append('rowAt_matches')
    step_terms.append('.equal [(0,1)] [(0,1)]');expected[200769]='⟨[(0,1),(0,-1)],[]⟩'
    body += ['def steps : List CompilerCompletion.Step := ['+', '.join(step_terms)+']',
        'def arithmeticRows : List Row := ['+', '.join(row_names[i] for i in block['arithmetic_rows'])+']',
        'theorem topological : CompilerCompletion.Topological [0,copy] [] steps := by',
        '  exact CompilerOrder.checked_order _ _ _ (by decide)',
        'theorem arithmetic_coverage : ∀ actual ∈ arithmeticRows, ∃ expected ∈ CompilerCompletion.emitted steps,',
        '    canonical p (unoutline copy actual.a) = canonical p expected.a ∧',
        '    canonical p (unoutline copy actual.b) = canonical p expected.b := by',
        '  intro actual member',
        '  simp only [arithmeticRows, List.mem_cons, List.not_mem_nil, or_false] at member',
        '  rcases member with '+' | '.join('rfl' for _ in block['arithmetic_rows'])]
    for index in block['arithmetic_rows']:
        body.append('  · exact ⟨'+expected[index]+', by decide, by decide, by decide⟩')
    body += ['variable {F : Type} [Field F] [CharP F p]',
        'def fixed (base : Nat → F) (column : Nat) : F := if column=0 ∨ column=copy then 1 else base column',
        'theorem constructive_arithmetic (base : Nat → F) :',
        '    ∃ rho : Nat → F, rho 0=1 ∧ rho copy=1 ∧ Satisfies rho arithmeticRows := by',
        '  have legal : CompilerCompletion.Legal (fixed base) steps := by',
        '    simp [CompilerCompletion.Legal, CompilerCompletion.Step.Legal, steps]',
        '  have result := CompilerCompletion.original_rows_complete (p:=p) (fixed base) steps [0,copy]',
        '    arithmeticRows copy topological legal (by decide) (by decide)',
        '    (by simp [fixed]) arithmetic_coverage',
        '  refine ⟨CompilerCompletion.run (fixed base) steps, ?_, ?_, result.1⟩',
        '  all_goals rw [result.2 _ (by decide)]; simp [fixed]',
        'theorem preserves_outside (base : Nat → F) (column : Nat)',
        '    (outside : column ∉ PoseidonCompletion.writes steps) :',
        '    CompilerCompletion.run base steps column = base column :=',
        '  PoseidonCompletion.run_outside base steps column outside']
    theorems+=['topological','arithmetic_coverage','constructive_arithmetic','preserves_outside']
    for i,n in enumerate(block['nodes']):
        body += [f'theorem operation_sound{i} (rho : Nat → F) (one : rho 0=1)',
            '    (four : (4:F) ≠ 0) (satisfied : Satisfies rho originalRows) :',
            f'    expressionValue rho output{i} = sourceValue (fun input => eval rho (inputTerms input))',
            f'      (fun index => expressionValue rho (prior{i} index)) operation{i} := by',
            '  have lowered := unoutline_rows_sound (p:=p) rho copy originalRows satisfied (by decide)',
            f'  exact node_certificate_sound unoutlined inputTerms prior{i} operation{i} output{i}',
            f'    certificate{i} rho one four lowered']
        theorems.append(f'operation_sound{i}')
    text=['-- GENERATED by generate_blocks.py. Typed cut operands; not a closed full source graph.',
        'import ShielddSecurity.CompilerCertificateTransport','import ShielddSecurity.CompilerOrderComposition',
        'import ShielddSecurity.CompilerSequenceCompletion','set_option maxHeartbeats 700000',
        'set_option maxRecDepth 4096','namespace '+namespace,'open Compiler',
        'def p : Nat := '+str(MODULUS),'def copy : Nat := 200692',
        'def inputTerms (input : Nat) : Linear := [(3+input,1)]']+declarations+body+['end '+namespace]
    # Array indexing proof uses its statically computed eight-or-fewer-row table.
    for name in theorems:text+=['set_option pp.all true in','#check @'+namespace+'.'+name,'#print axioms '+namespace+'.'+name]
    path=STAGE/'project/ShielddSecurity'/('TransferCost'+label+'01.lean')
    assert not path.exists();path.write_text('\n'.join(text)+'\n')
    summaries.append(dict(module=path.stem,source_sha256=sha(path),source_bytes=path.stat().st_size,
        arithmetic_node_indices=[n['id'] for n in block['nodes']],assertion=a,
        row_indices=block['rows'],arithmetic_row_indices=block['arithmetic_rows'],
        pooled_lcs=len(pool),maximum_lc_terms=max(map(len,pool)),named_audits=len(theorems),
        outlined_arithmetic_rows=[i for i in block['arithmetic_rows'] if i!=200769 and any(
            c==200692 for side in ['a','b'] for c,v in selected_rows[i][side])]))
assert sha(CAPTURE/'lowering-resume01.sqlite')==provenance['inputs']['lowering-resume01.sqlite']['sha256']
result=dict(status='generated',seconds=time.monotonic()-started,blocks=summaries,
    raw_source_identity=raw,binary_receipt=framing,source_nodes=nodes,source_assertions=assertions,
    selected_original_rows=selected_rows,baseline_provenance_sha256=sha(ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'),
    whole_source_graph_certificate=False,whole_row_indexed_instance=False,full_transfer='OPEN')
attempt=1
while (OUT/f'selection{attempt:02d}.json').exists():attempt+=1
target=OUT/f'selection{attempt:02d}.json';target.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='generated',modules=[x['module'] for x in summaries],seconds=result['seconds'])),flush=True)
