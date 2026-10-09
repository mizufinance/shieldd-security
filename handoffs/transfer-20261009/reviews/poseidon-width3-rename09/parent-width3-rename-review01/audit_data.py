"""Independent read-only DB comparison of the finite tail/page descriptor."""
import hashlib,json,sqlite3,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
P=ROOT/'outputs/mac-poseidon-width3-rename09/second-tail01.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
identity=sha(P);m=json.loads(P.read_text());started=time.monotonic()
result=json.loads(P.with_name('selection-result01.json').read_text())
assert result['status']=='passed' and identity==result['descriptor_sha256']
assert m['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
for name,expected in m['source_guards'].items():assert sha(ROOT/name)==expected
guard=json.loads(P.with_name('selection-guard01.json').read_text())
assert guard['status']=='passed' and guard['seconds']<=240 and guard['peak_group_rss_bytes']<=2*1024**3
assert sha(P.with_name('selection-guard01.log'))==guard['log_sha256']
db=ROOT/'work/parent-full-program/capture/lowering-resume01.sqlite'
conn=sqlite3.connect(db.resolve().as_uri()+'?mode=ro',uri=True);conn.execute('PRAGMA cache_size=-16384')
mod=int(m['modulus']);swap=lambda c:c+36886 if 24734<=c<25044 else c-36886 if 61620<=c<61930 else c
def canon(terms,copy):
    a={}
    for col,coef in terms:
        c=200692 if col==0 and copy else col;a[c]=(a.get(c,0)+coef)%mod
    return [[c,v] for c,v in sorted(a.items()) if v]
records={x['capture_index']:x for x in m['indexed_original_rows']}
assert set(records)==set(range(38400,39424))|{200769}
for i,x in records.items():
    aa,bb,origin=conn.execute('SELECT a,b,origin FROM rows WHERE id=?',(i,)).fetchone()
    assert x['unoutlined_a']==json.loads(aa) and x['unoutlined_b']==json.loads(bb) and x['origin']==json.loads(origin)
    for side in ['a','b']:assert x[side]==canon(x['unoutlined_'+side],i!=200769)
for i in range(38892,39192):
    x=records[i];assert x['source_reference_index']==i-36886
    aa,bb=conn.execute('SELECT a,b FROM rows WHERE id=?',(i-36886,)).fetchone()
    for side,old in [('a',aa),('b',bb)]:assert [[swap(c),v] for c,v in json.loads(old)]==x['unoutlined_'+side]
assert all(not 61630<=c<61930 for i in range(38400,38892) for side in ['a','b'] for c,v in records[i]['unoutlined_'+side])
assert m['prior_page_indices']==list(range(38400,38892)) and m['target_tail_indices']==list(range(38892,39192))
assert [x['round'] for x in m['rounds']]==list(range(2,65))
nodes=0
for r in m['rounds']:
    for phase in ['before','after']:
        for lc,ref in zip(r[phase],r[phase+'_raw_ports']):
            assert ref[0]==2
            current=json.loads(conn.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0]);old=json.loads(conn.execute('SELECT terms FROM nodes WHERE id=?',(ref[1]-342024,)).fetchone()[0])
            assert lc==current==[[swap(c),v] for c,v in old]
    for n in range(r['source_nodes'][0],r['source_nodes'][1]+1):
        old=conn.execute('SELECT op,lk,li,rk,ri,kind,terms FROM nodes WHERE id=?',(n-342024,)).fetchone();new=conn.execute('SELECT op,lk,li,rk,ri,kind,terms FROM nodes WHERE id=?',(n,)).fetchone()
        assert old[0]==new[0] and old[5]==new[5] and [[swap(c),v] for c,v in json.loads(old[6])]==json.loads(new[6])
        for k,i in [(1,2),(3,4)]:
            assert old[k]==new[k]
            if old[k]==2:assert old[i]+342024==new[i]
            else:
                assert old[k]==0
                assert conn.execute('SELECT value FROM constants WHERE id=?',(old[i],)).fetchone()==conn.execute('SELECT value FROM constants WHERE id=?',(new[i],)).fetchone()
        nodes+=1
assert nodes==1548 and sha(P)==identity
receipt={'schema':'parent-independent-finite-width3-tail-page-db-comparison-v1','descriptor_sha256':identity,'qualified_guard_sha256':sha(P.with_name('selection-guard01.json')),'parent_rows':1025,'tail_rows':300,'prior_page_rows':492,'round_boundary_pairs':63,'operations':nodes,'constant_operand_values_equal':True,'original_row_normalization_checked':True,'prior_page_write_support_separation':True,'seconds':time.monotonic()-started,'kernel_runs':0,'raw_stream_requalification':'producer exact qualified reader and guard inspected; parent DB comparison only','full_transfer':'OPEN'}
q=HERE/'data-audit01.json';assert not q.exists();q.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
