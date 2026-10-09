"""Finite upstream source/row budget observation; no kernel or native claim."""
import hashlib,json,sqlite3
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
census=ROOT/'work/parent-poseidon-call-census01/qualified01.json'
calls=json.loads(census.read_text())['calls'];target=calls[56];outer=calls[57]
assert target['width']==6 and target['domain']==17 and target['arity']==9 and target['IV']==2321
assert target['result']==[2,363983] and outer['inputs']==[[2,363983]]
database=ROOT/'work/parent-full-program/capture/lowering-resume01.sqlite'
c=sqlite3.connect(database.as_uri()+'?mode=ro',uri=True);c.execute('PRAGMA cache_size=-16384')
blockdata=[];allrows=set();maxterms=0
for block in target['permutations']:
    first=min(block['absorption_nodes']);last=block['round1_64_span'][1]
    nodes=c.execute('SELECT id,op,kind,terms,certificate FROM nodes WHERE id BETWEEN ? AND ? ORDER BY id',(first,last)).fetchall()
    assert len(nodes)==last-first+1
    rows=set();writes=set();constructors={}
    for i,op,kind,terms,certificate in nodes:
        cert=json.loads(certificate);lc=json.loads(terms);maxterms=max(maxterms,len(lc))
        constructors[cert['constructor']]=constructors.get(cert['constructor'],0)+1
        rows.update(cert['rows'])
        if cert['rows']:
            writes.update(t[0] for t in lc)
            writes.update(t[0] for t in cert.get('auxiliary',[]))
    assert rows==set(range(min(rows),max(rows)+1))
    allrows.update(rows)
    blockdata.append({'source_span':[first,last],'nodes':len(nodes),'arithmetic_row_span':[min(rows),max(rows)],'arithmetic_rows':len(rows),'materialized_write_span':[min(writes),max(writes)],'distinct_write_columns':len(writes),'constructors':constructors,'absorption_nodes':block['absorption_nodes'],'chunk_inputs':block['chunk_inputs']})
inputs=[]
for kind,i in target['inputs']:
    if kind==1:inputs.append({'port':[kind,i],'column':3+i,'scope':'original input, interpretation/native context OPEN'})
    else:
        k,terms=c.execute('SELECT kind,terms FROM nodes WHERE id=?',(i,)).fetchone()
        inputs.append({'port':[kind,i],'kind':k,'terms':json.loads(terms),'scope':'upstream node LC cut; semantic derivation OPEN'})
final=[]
for kind,i in target['final_state']:
    k,terms=c.execute('SELECT kind,terms FROM nodes WHERE id=?',(i,)).fetchone();final.append({'port':[kind,i],'kind':k,'terms':json.loads(terms)})
descriptor=json.loads((ROOT/'outputs/mac-poseidon-width3-call10/rounds02.json').read_text())
ports=descriptor['selected_rounds'][0]['external_ports']
matches=[x for x in ports if x['source_node']==363983]
assert len(matches)==1 and matches[0]['expression']['terms']==final[1]['terms']
result={'schema':'parent-domain17-nineinput-two-block-data-budget-v1','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','census_sha256':hashlib.sha256(census.read_bytes()).hexdigest(),'qualified_census_call_index':56,'domain':17,'arity':9,'IV':2321,'blocks':blockdata,'input_ports':inputs,'final_state':final,'max_node_linear_terms':maxterms,'arithmetic_rows':len(allrows),'rows_with_one_copy':len(allrows)+1,'result363983_equals_outer_input_terms':True,'outer_accepted_rows_with_copy':317,'proposed_join_row_count_with_shared_copy':len(allrows)+317,'kernel_runs':0,'native_correspondence':'OPEN','full_transfer':'OPEN'}
(H/'data-plan01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['input_ports','final_state']}))
