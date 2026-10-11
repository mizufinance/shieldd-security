"""Publish four reviewed source models, original identity maps and precise scope."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/end-to-end-20261011-01';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+8*1024*1024
tasks=[('end-to-end','windows-end-to-end-review01','TransferEndToEnd01',13)]
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
for n in ['review_cached_windows_end_to_end_endpoint01.py','windows-reviewed-ancestry-pool683-reports68-modules01.json','windows-cached-review-pipeline-test01.json','prepare_end_to_end_publication.py','end-to-end-rust-source-review01.json']:copy(J/n,Path('parent-review')/n)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/type/runtime/review bytes; no objects/raw logs/caches',files=records,omitted_raw_output=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Composed ordinary Host pipeline and failure-aware rollback',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules=selected,selected_complete_reports=13,scope='execute passes exact endBlock Host/Store to seal, then exact sealed Host/Store into actual commit; failure returns observed prefix Host/current queue; Whole returned ordinary pipeline derives actual InBlock/height/transfer/pending order, same Frozen and boundary through constructor injectivity, actual lock/intent/participant/capacity observations, final root/Idle/cleared identity/Ready/roots16/history/observed current health/reset; Completion Store matches captured-initial recovery under explicitly named ForwardPartitionFrames; main original participant final checks remain scoped to selected original recovery model; rollback invokes exact recoverCurrent on existing Store then actual rebuild outcome; recovery error and rebuild error preserve original Host phase/active/block identity while retaining actual writer/Store progress; Successful rollback requires returned actual rebuilt application; reaches Idle/deferredBatch/selected Ready/current recovered roots; Finite pending codec and component finalization field contract to connect earlier whole delivery inputs; Native actual temporal ghost/snapshot/storage/lock/Arc/Clone/typed root/version/height/serde/ownership/concurrency/library correspondence; Snapshot raw/proof coherence and separate ICS23 verifier soundness; external Host commitment authentication remains a distinct path; Actual forward native partition frame correspondence for original participant recovery; current recovery direct final checks differ; OS durability/genuine native execution, initialization branches, full circuit/wholeTransfer/final replay',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs','.lean'))];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for tree in D.rglob('tree.rs'):
 if any(line.rstrip(b'\r')!=line.rstrip(b'\r').rstrip(b' \t')for line in tree.read_bytes().splitlines()):
  a.write_text(a.read_text()+f'\n{tree.relative_to(G)} whitespace=-blank-at-eof,-blank-at-eol\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('end-to-end-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'end-to-end-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
