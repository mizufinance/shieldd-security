"""Read-only exact source regeneration, captured data comparison and history review."""
from pathlib import Path
import hashlib,json,re,sqlite3,shutil,subprocess
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-registered-audit71-kernel-result01'
checked={}
def read(pin):
 p=Path(pin['path']);b=p.read_bytes();assert len(b)==pin['bytes'] and hashlib.sha256(b).hexdigest()==pin['sha256'],p
 checked[str(p)]=pin;return b
Q=W/'mac-registered-audit70-data01/qualification01.json';qb=Q.read_bytes();assert hashlib.sha256(qb).hexdigest()=='ee64c753d8a42420995ec074542a2b33e2a7d2604c885b2cfee4a55652441009'
q=json.loads(qb);db=W/'parent-full-program/capture/lowering-resume01.sqlite';before=(db.stat().st_size,db.stat().st_mtime_ns);assert list(before)==q['db_stat']
c=sqlite3.connect(db.as_uri()+'?mode=ro&immutable=1',uri=True);c.execute('PRAGMA cache_size=-8192');c.execute('PRAGMA query_only=ON')
for v in q['rows']:
 r=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(v['index'],)).fetchone();assert dict(index=v['index'],a=json.loads(r[0]),b=json.loads(r[1]),origin=json.loads(r[2]))==v
for v in q['nodes']:
 r=c.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(v['id'],)).fetchone();assert dict(id=v['id'],op=r[0],left=[r[1],r[2]],right=[r[3],r[4]],kind=r[5],terms=json.loads(r[6]),certificate=json.loads(r[7]))==v
for v in q['assertions']:
 r=c.execute('SELECT lk,li,rk,ri,certificate FROM assertions WHERE id=?',(v['id'],)).fetchone();assert dict(id=v['id'],left=[r[0],r[1]],right=[r[2],r[3]],certificate=json.loads(r[4]))==v
for v in q['constants']:
 assert c.execute('SELECT value FROM constants WHERE id=?',(v['id'],)).fetchone()[0]==v['value']
c.close();assert before==(db.stat().st_size,db.stat().st_mtime_ns)
assert [v['index'] for v in q['rows']]==list(range(262,322))+list(range(178048,178083))
assert [v['id'] for v in q['assertions']]==list(range(94,129))
mods=json.loads((P/'qualified-modules01.json').read_bytes());audit=json.loads((J/'audit-result01.json').read_bytes());names={e['module']:[a['name'] for a in e['audits']] for e in audit['modules']}
T=J/'source-replay01';T.mkdir();D=T/'mac-registered-audit70-data01';D.mkdir();shutil.copyfile(Q,D/Q.name)
local=[]
for e in mods:
 n=e['name'];source=read(e['source']).decode();clean=re.sub(r'/-.*?-/', '',source,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 public=[]
 for m in re.finditer(r'^(?P<mods>(?:(?:noncomputable|private|protected|local)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class|instance)\s+(?P<name>[\w.]+)',clean,re.M):
  full='ShielddSecurity.'+n+'.'+m['name'];qual=m['mods'].split()
  if 'local' in qual:local.append(full)
  elif 'private' not in qual:public.append(full)
 assert public==names[n],(n,public,names[n])
 assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',clean)
 S=Path(e['source']['path']).parents[2];R=T/S.name;R.mkdir()
 for file in ['generate.py','template.lean','input-pins01.json','dependencies01.json']:
  if (S/file).is_file():shutil.copyfile(S/file,R/file)
 run=subprocess.run(['python3','-I','-B','-S',str(R/'generate.py')],capture_output=True,text=True,timeout=60);assert run.returncode==0,run.stderr
 assert (R/'source-root/ShielddSecurity'/(n+'.lean')).read_bytes()==read(e['source']),n
for v in json.loads((P/'maintained-references01.json').read_bytes()):read(v)
h=json.loads((P/'attempt-history01.json').read_bytes());receipts=[json.loads(read(v)) for v in h['receipts']];assert len(receipts)==h['all_attempts']==759 and sum(r['status']=='passed' for r in receipts)==h['passed']==733
assert abs(sum(r['lean_seconds'] for r in receipts)-h['all_lean_seconds'])<1e-8
rejected=[]
for pin,r in zip(h['receipts'],receipts):
 if r['status']=='passed':continue
 assert r['status']=='failed' and r['cleanup']['clean'] and r['error'] is not None
 for key in ['source','stdout','stderr']:
  if r.get(key) is not None:read(r[key])
 rejected.append(dict(receipt=pin,module=r['module'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],exit=r['exit'],error=r['error'],cleanup_clean=True,scope='Rejected attempt; no semantic negative result'))
assert [r['receipt'] for r in rejected]==[r['receipt'] for r in h['failed']]
assert all(e['receipt'] in h['receipts'] for e in mods)
out=dict(kind='Independent source regeneration, original narrow SQLite comparison and complete original receipt history; no Lean/native execution',modules=3,reports=23,local_nonexported_declarations=local,source_replay_exact=True,qualification=dict(path=str(Q),bytes=len(qb),sha256=hashlib.sha256(qb).hexdigest()),original_rows=95,original_nodes=72,original_assertions=35,original_constants=45,db_stat_unchanged=True,history_attempts=759,history_passed=733,rejected=rejected,pins_rehashed=len(checked),scope='Actual 60 arithmetic positions and 35 assertions derive ten zero primitives and five regulated pair-exclusion guards. Canonical transport has explicit small-coordinate bounds. No legal-witness constructor or full Transfer/native conclusion in this packet.',full_transfer='OPEN')
(J/'source-data-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['rejected','qualification']}))
