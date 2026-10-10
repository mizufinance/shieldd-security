from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).resolve().parent;P=J/'packet01';G=J.parent.parent/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/concrete-model-cofactor-20261010-01'
assert not D.exists();D.mkdir(parents=True)
excluded=[]
for source in sorted(P.rglob('*')):
 if not source.is_file():continue
 relative=source.relative_to(P)
 if source.suffix=='.jsonl':excluded.append(str(relative));continue
 assert source.suffix not in ['.olean','.ir','.ilean','.txt','.stdout','.stderr']
 target=D/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
for name in ['audit_endpoint.py','audit-result01.json','generator-review01.json','runner-review01.json','import-review01.json','endpoint-review.md','prepare_publication.py','transport-verification01.json']:
 target=D/'parent-review'/name;target.parent.mkdir(exist_ok=True);shutil.copyfile(J/name,target)
(D/'README.md').write_text('Scoped actual concrete Edwards/Mathlib curve model and closed cofactor join for runtime844389ee069e1fb2e576708842d0b389b4d9a44a.18 sources/92 complete type and standard-axiom reports. See parent-review/endpoint-review.md for the remaining byte-writer, key-admission, native SDK and full Transfer obligations. Raw event/compiler logs, objects, caches, toolchains and composed workspaces are excluded.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='exact source/evidence publication, no parent kernel replay',files=records,excluded_raw_event_logs=excluded,full_transfer='OPEN'),indent=2)+'\n')
(J/'publication-payload01.json').write_text(json.dumps(dict(path=str(D),files=len(records)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),excluded=excluded),indent=2)+'\n')
print(json.dumps(dict(files=len(records)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),excluded_logs=len(excluded))))
