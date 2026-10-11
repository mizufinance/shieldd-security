"""Independent readonly captured high-limb DATA review; no Lean/native build."""
from pathlib import Path
import sqlite3,json,hashlib
D=Path(__file__).parent;J=D.parent;W=J.parent;Q=W/'mac-registry-high-limb120-data02/selected-data01.json';b=Q.read_bytes();assert hashlib.sha256(b).hexdigest()=='c216e975ff3d0834e7a6587cce7fbc04179543b6205ac37ac41e9c5a6799196a';assert b==(W/'parent-high-limb120-data-replay01/selected-data01.json').read_bytes();q=json.loads(b);db=Path(q['database']['path']);st=[db.stat().st_size,db.stat().st_mtime_ns];assert st==[q['database']['bytes'],q['database']['mtime_ns']]
c=sqlite3.connect(db.as_uri()+'?mode=ro&immutable=1',uri=True);c.execute('PRAGMA cache_size=-8192');c.execute('PRAGMA query_only=ON');P=52435875175126190479447740508185965837690552500527637822603658699938581184513
nodes={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=json.loads(r[7]),certificate=json.loads(r[8]))for r in c.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id BETWEEN 124480 AND 125374')};assert len(nodes)==q['source_nodes']==895;assert hashlib.sha256(json.dumps(nodes,sort_keys=True,separators=(',',':')).encode()).hexdigest()==q['source_node_lc_sha256'];assert nodes[124733]['terms']==[[599+i,2**i]for i in range(127)];assert nodes[124987]['terms']==[[344+i,2**i]for i in range(127)]
for key,value in q['constants'].items():assert int(c.execute('SELECT value FROM constants WHERE id=?',(int(key),)).fetchone()[0],16)==value
normalize=lambda terms:sorted([[column,value%P]for column,value in terms if value%P]);outline=lambda terms:sorted([[200692 if column==0 else column,value]for column,value in terms]);assert len(q['rows'])==130
for offset,e in enumerate(q['rows']):
 index=178893+offset;assert e['index']==index and e['assertion']==939+offset
 if offset<128:
  column=981 if offset==0 else 982+offset;a=[[column,1]];z=a
 elif offset==128:a=normalize([[982,-1]]+[[983+i,2**i]for i in range(127)]);z=[]
 else:a=normalize([[344+i,2**i]for i in range(127)]+[[599+i,-2**i]for i in range(127)]+[[981,2**127],[982,-1]]);z=[]
 raw=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(index,)).fetchone();aa,zz,origin=map(json.loads,raw);assert aa==a==e['a']and zz==z==e['b'];assert e['outlined_a']==outline(a)and e['outlined_b']==outline(z);assert origin==e['origin']==dict(kind='assertion',id=939+offset,role='fusedSquare'if offset<128 else'linear')
 assertion=c.execute('SELECT lk,li,rk,ri,certificate FROM assertions WHERE id=?',(939+offset,)).fetchone();cert=json.loads(assertion[4]);assert cert==e['certificate']and cert['left']==list(assertion[:2])and cert['right']==list(assertion[2:4])and cert['rows']==[index]
for key in ['binary_qualification','range_source','registry_source']:
 pin=q[key];data=Path(pin['path']).read_bytes();assert len(data)==pin['bytes']and hashlib.sha256(data).hexdigest()==pin['sha256']
c.close();assert st==[db.stat().st_size,db.stat().st_mtime_ns]
out=dict(status='PASSED',original_extraction_replayed_exact=True,selected_data_sha256=hashlib.sha256(b).hexdigest(),raw_nodes=895,constants=len(q['constants']),actual_assertion_rows=130,positions=[178893,179022],source_input_high_asset=[599,726],source_input_high_value=[344,471],borrow=981,difference=982,private_difference_bits=[983,1110],every_row_and_original_certificate_exact=True,independent_signed_recipe_match=True,database_metadata_preserved=True,scope='DATA only; numeric/high-bit/kernel construction qualified separately; no native/fullTransfer result');(D/'data-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
