"""Independently compare finite descriptor ports/rows/prefix records to pinned DB."""
import hashlib,json,sqlite3
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];O=ROOT/'outputs/mac-poseidon-width6-upstream11';p=O/'upstream01.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(p)=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e';d=json.loads(p.read_text())
c=sqlite3.connect((ROOT/'work/parent-full-program/capture/lowering-resume01.sqlite').as_uri()+'?mode=ro',uri=True);c.execute('PRAGMA cache_size=-16384')
assert d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
params=ROOT/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381-wide.json'
assert sha(params)==d['parameter_sha256'] and json.loads(params.read_text())==d['parameters']
prefix=set()
for scope in d['prefix_scopes']:
    for node in scope['nodes']:
        i=node['source_node'];op,lk,li,rk,ri,kind,terms,cert=c.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(i,)).fetchone()
        assert op==node['operation'] and [lk,li]==node['left'] and [rk,ri]==node['right']
        assert {'kind':kind,'terms':json.loads(terms)}==node['expression'] and json.loads(cert)==node['certificate'];prefix.add(i)
ports=0
for block in d['blocks']:
    for rnd in block['rounds']:
        for phase,refs in rnd['raw_ports'].items():
            expected=rnd['ports'][phase];assert len(refs)==len(expected)==6
            for ref,lc in zip(refs,expected):
                if ref[0]=='native':assert lc==([] if ref[1]==0 else [[0,ref[1]]])
                else:
                    assert ref[0]==2
                    kind,terms=c.execute('SELECT kind,terms FROM nodes WHERE id=?',(ref[1],)).fetchone()
                    assert kind=='linear' and json.loads(terms)==lc
                ports+=1
row_indices=[]
for row in d['indexed_original_rows']:
    i=row['capture_index'];a,b,origin=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone()
    assert json.loads(a)==row['unoutlined_a'] and json.loads(b)==row['unoutlined_b'] and json.loads(origin)==row['origin'];row_indices.append(i)
assert sorted(row_indices)==list(range(38040,38876))+[200769] and len(row_indices)==len(set(row_indices))==837
input_terms=[]
for kind,i in d['input_ports']:
    if kind==1:input_terms.append([[3+i,1]])
    else:input_terms.append(json.loads(c.execute('SELECT terms FROM nodes WHERE id=?',(i,)).fetchone()[0]))
assert input_terms==d['input_terms']
prior=d['blocks'][0]['rounds'][-1]['ports']['after'];assert prior==d['blocks'][1]['before_absorption']
new=d['blocks'][1]['rounds'][-1]['ports']['after'][1]
outer=json.loads((ROOT/'outputs/mac-poseidon-width3-call10/rounds02.json').read_text())
assert new==next(x['expression']['terms'] for x in outer['selected_rounds'][0]['external_ports'] if x['source_node']==363983)
result={'schema':'parent-upstream11-exact-descriptor-port-row-data-review-v1','descriptor_sha256':sha(p),'prefix_node_records':len(prefix),'phase_port_expressions':ports,'independent_rounds':130,'actual_rows_including_copy':837,'two_block_boundary_exact':True,'result363983_equals_accepted_outer_input':True,'input_ports':9,'parameter_actual_bytes_and_json_checked':True,'kernel_runs':0,'raw_stream_replay':False,'full_transfer':'OPEN'}
(H/'descriptor-audit01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
