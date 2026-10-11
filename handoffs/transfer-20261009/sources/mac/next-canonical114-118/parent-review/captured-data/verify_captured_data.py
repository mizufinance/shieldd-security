"""Reproducible narrow readonly comparison DATA check; no theorem/native execution."""
from pathlib import Path
import hashlib,json,sqlite3
J=Path(__file__).parent.parent;W=J.parent
qpath=W/'mac-next-comparison115-data01/selected-data01.json'
b=qpath.read_bytes();assert hashlib.sha256(b).hexdigest()=='1305684d017e23bdf386df162a38f0d4bd8b3c51d770c05b3c11a0223e59e4e4'
assert b==(W/'parent-next-comparison115-data-replay01/selected-data01.json').read_bytes()
q=json.loads(b);db=Path(q['database']);before=[db.stat().st_size,db.stat().st_mtime_ns];assert before==q['database_stat']
c=sqlite3.connect(db.as_uri()+'?mode=ro&immutable=1',uri=True);c.execute('PRAGMA cache_size=-8192');c.execute('PRAGMA query_only=ON')
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;copy=200692
assert c.execute('SELECT count(*) FROM nodes WHERE id BETWEEN ? AND ?',q['source_span']).fetchone()[0]==q['source_nodes']==2295
outline=lambda ts:sorted([[copy if n==0 else n,v]for n,v in ts])
assert len(q['entries'])==254
for i,e in enumerate(q['entries'],1):
 node=122184+9*i+7;raw=c.execute('SELECT lk,li,terms,certificate FROM nodes WHERE id=?',(node,)).fetchone();assert raw[0]==2
 left=json.loads(c.execute('SELECT terms FROM nodes WHERE id=?',(raw[1],)).fetchone()[0]);after=json.loads(c.execute('SELECT terms FROM nodes WHERE id=?',(node+1,)).fetchone()[0]);cert=json.loads(raw[3])
 assert outline(left)==e['before']and outline(after)==e['after']and e['bitColumn']==726+i and e['maximumBit']==bool((P-1)>>i&1)
 assert json.loads(raw[2])==[[e['pivot'],1]]and cert['auxiliary']==[[e['auxiliary'],1]]and cert['rows']==[r['index']for r in e['rows']]
 for r in e['rows']:
  a,z,o=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(r['index'],)).fetchone();assert outline(json.loads(a))==r['a']and json.loads(z)==r['b']and json.loads(o)==r['origin']and r['origin']['id']==node
constants={n:c.execute('SELECT value FROM constants WHERE id=?',(n,)).fetchone()[0]for n in q['constant_ids']}
assert hashlib.sha256(json.dumps(constants,sort_keys=True,separators=(',',':')).encode()).hexdigest()==q['constants_sha256'];c.close();assert before==[db.stat().st_size,db.stat().st_mtime_ns]
for k in ['binary_qualification','source_encoding','source_comparison']:
 pin=q[k];v=Path(pin['path']).read_bytes();assert len(v)==pin['bytes']and hashlib.sha256(v).hexdigest()==pin['sha256']
old=json.loads((W/'mac-registry-value-comparison102-source01/selected-data01.json').read_bytes())
def rename(column):return column+510 if 216<=column<471 else column+1016 if 32246<=column<32754 else column
mapped=lambda terms:sorted([[rename(column),value]for column,value in terms])
for prior,target in zip(old['entries'],q['entries']):
 assert rename(prior['bitColumn'])==target['bitColumn']and prior['maximumBit']==target['maximumBit']
 assert mapped(prior['before'])==target['before']and mapped(prior['after'])==target['after']
 assert rename(prior['pivot'])==target['pivot']and rename(prior['auxiliary'])==target['auxiliary']
 for source,row in zip(prior['rows'],target['rows']):assert row['index']==source['index']+1016 and mapped(source['a'])==row['a']and mapped(source['b'])==row['b']
assert rename(copy)==copy
out=dict(status='PASSED',exact_original_extraction=True,entries=254,arithmetic_positions=[10524,11031],rows=508,raw_nodes=2295,raw_span=q['source_span'],constants=len(constants),selected_data_sha256=hashlib.sha256(b).hexdigest(),database_metadata_preserved=True,field_maximum='p-1',source_encoding=q['source_encoding'],source_comparison=q['source_comparison'],selected_row_renaming_exact=True,renaming_scope='Only selected row transport and rho composition; no global injectivity or frame claim',scope='Captured DATA only; full Transfer/native OPEN')
(Path(__file__).parent/'data-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
