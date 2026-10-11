"""Publish four reviewed source models, original identity maps and precise scope."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/record-read-bound-20261011-01';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+8*1024*1024
tasks=[('record-read-bound','windows-record-read-bound-review01','TransferRecordReadBound01',8)]
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
for n in ['review_record_read_generation01.py','review_cached_windows_recovery_ancestry_endpoint01.py','windows-reviewed-ancestry-pool584-reports59-modules01.json','windows-cached-review-pipeline-test01.json','prepare_record_read_bound_publication.py','record-read-rust-source-review01.json']:copy(J/n,Path('parent-review')/n)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/type/runtime/review bytes; no objects/raw logs/caches',files=records,omitted_raw_output=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Source recovery record read derives exact observed bounded bytes',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules=selected,selected_complete_reports=8,scope='Generated exact source MAX_RECORD_BYTES expression 4*1024*1024 and checked source read_record take(MAX_RECORD_BYTES+1)/read_to_end/returned byte length check. Source take limit is one beyond record cap and proved below 32/64-bit word ranges. Whole returned record derives exact observed read_to_end bytes at source take limit and length at most 4194304; oversized returned bytes and read errors refuse without default records. Eight reports (four data/program definitions, four proofs), maintained generator plus byte-identical independent regeneration; finite/physical/strict audit guards unchanged. Native File/Take/Read partial read semantics, allocation/typed u8/usize-to-u64 supported word embedding/ownership/serde/OS state and whole input consumption remain interfaces. Model Nat length reflects native cast only on supported typed 32/64-bit domain. No native/control/full Transfer certification and no semantic-negative-control credit from formal refusal proofs. All eight declarations retain original complete type/axiom reports. Source bounded read success derives actual callback bytes and checked size; unavailable reads and oversized observed bytes refuse. Native Read/Take allocation, partial consumption, serde, OS, owner and representation remain explicit interfaces. Zero native/control/full certification credit.',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs','.lean'))];hand=[p for p in hand if not p.endswith('.lean')];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for tree in D.rglob('tree.rs'):
 if any(line.rstrip(b'\r')!=line.rstrip(b'\r').rstrip(b' \t')for line in tree.read_bytes().splitlines()):
  a.write_text(a.read_text()+f'\n{tree.relative_to(G)} whitespace=-blank-at-eof,-blank-at-eol\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('record-read-bound-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'record-read-bound-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
