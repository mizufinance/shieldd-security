"""Independent exact DB comparison for the prefix descriptor; no kernel run."""
import hashlib,json,sqlite3,time
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];O=R/'outputs/mac-poseidon-width3-call10';P=O/'rounds02.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();identity=sha(P);m=json.loads(P.read_text());start=time.monotonic()
assert identity=='01b68f32bf6896a6122805713cdd5448105d2aab2da056699c9d35dd57f162ff'
assert m['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
for n,h in m['source_guard_identities'].items():assert sha(R/n)==h
parameter=R/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381.json';assert sha(parameter)==m['parameter_sha256']=='f45040142a56e16bb8480f1f6648621d32f456646cfaf77beca2b05a6bb12742';assert json.loads(parameter.read_text())==m['parameters']
c=sqlite3.connect((R/'work/parent-full-program/capture/lowering-resume01.sqlite').resolve().as_uri()+'?mode=ro',uri=True);c.execute('PRAGMA cache_size=-16384');seen=set();constants=set();cuts=set()
for scope in m['selected_rounds']:
    for n in scope['nodes']:
        i=n['source_node'];op,lk,li,rk,ri,kind,terms,cert=c.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(i,)).fetchone()
        assert n['operation']==op and n['left']==[lk,li] and n['right']==[rk,ri] and n['expression']=={'kind':kind,'terms':json.loads(terms)} and n['certificate']==json.loads(cert);seen.add(i)
    for v in scope['constants']:
        i=v['source_constant'];value=c.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0];assert v['canonical_scalar']==value and v['integer']==int(value,16);constants.add(i)
    for port in scope['external_ports']:
        i=port['source_node'];kind,terms=c.execute('SELECT kind,terms FROM nodes WHERE id=?',(i,)).fetchone();assert port['expression']=={'kind':kind,'terms':json.loads(terms)};cuts.add(i)
assert seen==set(range(364032,364076)) and len(constants)==26 and len(cuts)==4
mod=int(m['modulus']);copy=m['constant_copy']
def canon(terms,link):
    out={}
    for col,v in terms:
        col=copy if link and col==0 else col;out[col]=(out.get(col,0)+v)%mod
    return [[col,v] for col,v in sorted(out.items()) if v]
indices=[]
for row in m['indexed_original_rows']:
    i=row['capture_index'];a,b,origin=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone();assert row['unoutlined_a']==json.loads(a) and row['unoutlined_b']==json.loads(b) and row['origin']==json.loads(origin)
    for side in ['a','b']:assert row[side]==canon(row['unoutlined_'+side],i!=200769)
    indices.append(i)
assert indices==list(range(38876,38892))+[200769]
match=json.loads((O/'reproduced-prefix-match02.json').read_text());assert match['domain']==18 and match['arity']==1 and match['IV']==274 and match['input_ports']==[[2,363983]] and match['nodes']==[364032,364075]
assert len(match['controls'])==8 and all(v['rejected'] for v in match['controls'])
suffix=json.loads((R/'outputs/mac-poseidon-width3-rename09/second-tail01.json').read_text());last=m['selected_rounds'][1]['phase_ports']['after_mds']
for ref,expected in zip(last,suffix['rounds'][0]['before']):assert ref[0]==2 and json.loads(c.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0])==expected
assert sha(P)==identity
result={'schema':'parent-exact-width3-domain18-prefix-db-data-comparison-v1','descriptor_sha256':identity,'source_nodes':44,'constants':26,'external_cut_ports':4,'rows_including_copy':17,'round1_after_equals_suffix_before_data':True,'domain':18,'arity':1,'IV':274,'cut_input':363983,'parameter_actual_bytes_and_json_checked':True,'producer_matcher_data_controls':8,'seconds':time.monotonic()-start,'parent_raw_stream_replay':False,'kernel_runs':0,'full_transfer':'OPEN'}
p=H/'data-audit01.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
