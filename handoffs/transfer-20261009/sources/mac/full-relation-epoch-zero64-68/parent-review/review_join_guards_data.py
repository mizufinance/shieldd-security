"""Review exact guard changes, diagnostic parsing and fourteen original rows."""
from pathlib import Path
import ast,difflib,hashlib,json,re,sqlite3
W=Path(__file__).parent.parent;J=Path(__file__).parent
def sha(b):return hashlib.sha256(b).hexdigest()
base=W/'mac-full-arithmetic45-execution21/maintained/guard.py';tree=ast.parse(base.read_text());baseline={n.name:ast.dump(n)for n in tree.body if isinstance(n,ast.FunctionDef)}
guards=[]
for n in range(26,35):
 p=W/('mac-full-arithmetic45-execution'+str(n))/'maintained/guard.py';b=p.read_bytes();t=ast.parse(b.decode());functions={n.name:ast.dump(n)for n in t.body if isinstance(n,ast.FunctionDef)};changed=sorted(n for n in baseline if functions[n]!=baseline[n]);assert set(changed)<={'source_check','audit_log','fixed_check','bounds','launch_reserve'};assert set(functions)==set(baseline)
 delta=''.join(difflib.unified_diff(base.read_text().splitlines(True),b.decode().splitlines(True),fromfile='accepted-execution21',tofile=p.parent.parent.name))
 guards.append(dict(path=str(p),bytes=len(b),sha256=sha(b),changed_functions=changed,exact_delta=delta))
fn=next(n for n in t.body if isinstance(n,ast.FunctionDef)and n.name=='audit_log')
def require(ok,context):
 if not ok:raise ValueError(context)
ns=dict(re=re,sha=sha,require=require);exec(compile(ast.Module(body=[fn],type_ignores=[]),str(p),'exec'),ns)
mods=json.loads((W/'mac-registry-epoch-semantic66-kernel-result01/qualified-modules01.json').read_bytes());e=next(e for e in mods if e['name']=='TransferCore');receipt=json.loads(Path(e['receipt']['path']).read_bytes());output=Path(receipt['stdout']['path']).read_bytes();names=[a['name']for a in receipt['audits']];assert ns['audit_log'](output,names)==receipt['audits']
refusals=[]
for s in [b'/tmp/exact.lean:1:1: error: malformed\n',b'warning: unexpected\n',b'trace: diagnostic\n',b'uncaught exception\n']:
 try:ns['audit_log'](s+output,names)
 except ValueError:refusals.append(s.decode().strip())
 else:raise AssertionError('diagnostic accepted')
aliases={};visited=set();histories=[]
def history(r):
 key=(r['path'],r['sha256'])
 if key in visited:return
 visited.add(key);b=Path(r['path']).read_bytes();assert len(b)==r['bytes']and sha(b)==r['sha256'];d=json.loads(b)
 for parent in d.get('parents',[]):history(parent)
 for k,v in d.get('historical_aliases',{}).items():
  if k in aliases:assert aliases[k]==v
  aliases[k]=v
 histories.append(r)
config=json.loads((W/'mac-full-arithmetic45-execution34/config01.json').read_bytes());history(config['carried_failure'])
out=dict(kind='Read-only original guard/delta and parser review; synthetic parser refusals are not semantic negative controls',guards=guards,physical_changes='None: one thread/M2048/4GiB RSS/240seconds/15percent RAM/2GiB disk floor/finite heartbeats remain unchanged',diagnostic_change='Anchored diagnostic detection avoids the ordinary trace binder while complete output parsing still rejects unexplained output',style_option='Only linter.dupNamespace=false added',import_check='Fresh module must have every custom/official import in the exact protected closure or an already completed owned module',history_change='Recursive exact-pinned parent manifests avoid copying historical aliases; all alias collisions checked equal',history_manifests=histories,history_aliases=len(aliases),finite_disk_metadata_change='Batch file cap1to2GiB and matching launch reserve1008to2032MiB; physical disk floor and RAM/RSS constraints unchanged',parser_original_reports=len(names),parser_refusals=refusals,full_transfer='OPEN')
(J/'join-guard-review01.json').write_text(json.dumps(out,indent=2)+'\n')
Q=W/'mac-captured-zero-tests67-data01/qualification01.json';q=json.loads(Q.read_bytes());db=Path(q['db']);before=(db.stat().st_size,db.stat().st_mtime_ns);assert list(before)==q['metadata'];c=sqlite3.connect(db.as_uri()+'?mode=ro&immutable=1',uri=True);c.execute('PRAGMA cache_size=-8192');c.execute('PRAGMA query_only=ON')
for r in q['rows']:
 raw=c.execute('SELECT a,b,origin FROM rows WHERE id=?',(r['index'],)).fetchone();assert [json.loads(raw[0]),json.loads(raw[1])]==r['original']and json.loads(raw[2])==r['origin']
for r in q['nodes']:
 raw=c.execute('SELECT op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE id=?',(r['source'],)).fetchone();assert dict(source=r['source'],op=raw[0],left=[raw[1],raw[2]],right=[raw[3],raw[4]],kind=raw[5],terms=json.loads(raw[6]),certificate=json.loads(raw[7]))==r
c.close();assert before==(db.stat().st_size,db.stat().st_mtime_ns)
assert [r['index']for r in q['rows']]==list(range(262,270))+list(range(178048,178054));assert [r['source']for r in q['nodes']]==list(range(431,443))
(J/'global-zero68-review01/data-review01.json').write_text(json.dumps(dict(kind='Independent narrow original readonly DB comparison; no new full database hash or semantic result',qualification=dict(path=str(Q),bytes=Q.stat().st_size,sha256=sha(Q.read_bytes())),rows=14,nodes=12,db_stat_unchanged=True,full_transfer='OPEN'),indent=2)+'\n')
print(json.dumps(dict(guards=len(guards),parser_reports=len(names),parser_refusals=len(refusals),history_manifests=len(histories),history_aliases=len(aliases),original_rows=14,original_nodes=12)))
