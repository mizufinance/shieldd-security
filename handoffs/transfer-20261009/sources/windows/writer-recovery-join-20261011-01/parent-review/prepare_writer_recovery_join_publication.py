"""Publish four reviewed source models, original identity maps and precise scope."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/writer-recovery-join-20261011-01';assert not D.exists() or all((D/e['path']).is_file() and len((D/e['path']).read_bytes())==e['bytes'] and hashlib.sha256((D/e['path']).read_bytes()).hexdigest()==e['sha256'] for e in json.loads((D/'publication-manifest01.json').read_bytes())['files']);assert shutil.disk_usage(W).free>2147483648+8*1024*1024
tasks=[('writer-recovery-join','windows-writer-recovery-join-review01','TransferWriterRecoveryJoin01',6)]
records=[];omitted=[];selected={}
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,n):
 b=p.read_bytes();assert shutil.disk_usage(W).free>2147483648+4*1024*1024+len(b);t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b);assert t.read_bytes()==b
 records.append(dict(original=dict(path=str(p),bytes=len(b),sha256=sha(b)),publication=dict(path=str(t.relative_to(D)),bytes=len(b),sha256=sha(b))))
for label,name,module,count in tasks:
 R=J/name;P=R/'packet01';review=json.loads((R/'endpoint-audit-review01.json').read_bytes());assert review['fresh_modules']==1 and review['fresh_reports']==count
 for p in sorted(P.rglob('*')):
  if not p.is_file():continue
  if p.name in ['compiler-output.txt','stdout.txt','stderr.txt']:omitted.append(dict(original=dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p.read_bytes())),reason='Raw compiler output excluded; complete qualified reports and structured rejection diagnostics retained'));continue
  copy(p,Path(label)/p.relative_to(P))
 for n in ['endpoint-audit-review01.json','transport-verification01.json','decode_transport.py','preparation-merge-review01.json','ancestor-source-mapping-review01.json','source-regeneration-review01.json','semantic-source-review01.json']:
  if(R/n).is_file():copy(R/n,Path('parent-review')/label/n)
 selected[module]=dict(path=str(Path(label)/'source/ShielddSecurity'/(module+'.lean')),complete_reports=count)
for n in ['prepare_recovery_ancestry_cache01.py','review_cached_windows_recovery_ancestry_endpoint01.py','windows-reviewed-ancestry-pool570-reports57-modules01.json','windows-cached-review-pipeline-test01.json','prepare_writer_recovery_join_publication.py','writer-recovery-rust-source-review01.json']:copy(J/n,Path('parent-review')/n)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/type/runtime/review bytes; no objects/raw logs/caches',files=records,omitted_raw_output=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Source writer completion composes exact original recovery boundary, history and observed health',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules=selected,selected_complete_reports=6,scope='Model composition of actual-source PermanentWriter participant/commit/capacity order with independently qualified original BankRecovery10, reused once with original source/object/full type/axiom reports and shared Readback17 unchanged. Recovery environment denotes independently observed store at completion invocation. Completion callback reports recovery returned error status; completed source participants derive clean recovery, ready/current roots/exact frozen boundary/16 roots/retained-history validity and independently observed partition health. Whole returned source commit derives same Ready owner/returned boundary and observed recovered store boundary/roots. Capacity error preserves Ready/new boundary and completed recovery; failed recovery prevents participant completion and blocks owner API status. Six fresh reports (two program definitions, four proofs), 570 original inherited reports/57 owned modules, strict finite/physical guards unchanged. Native prior participant-to-recovery state threading, current poison snapshots/intermediate readers, source complete/recovery/rollback/partition frames, locks/owner/Clone/typed values/physical I/O/durability remain explicit correspondence obligations; original recovery model is not relabeled native proof. No native/control/full Transfer certification or inferred healthy partitions/error rollback. All six fresh declarations and original BankRecovery10 have complete original type/axiom reports. Shared Readback17 is unchanged and selected once. Native temporal state threading/current poison snapshots/partition frames/locks/IO/durability remain explicit rather than inferred from modeled adapter success. Recovery health stays independently observed; zero native/control/full certification credit.',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs','.lean'))];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for tree in D.rglob('tree.rs'):
 if any(line.rstrip(b'\r')!=line.rstrip(b'\r').rstrip(b' \t')for line in tree.read_bytes().splitlines()):
  a.write_text(a.read_text()+f'\n{tree.relative_to(G)} whitespace=-blank-at-eof,-blank-at-eol\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('writer-recovery-join-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'writer-recovery-join-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
