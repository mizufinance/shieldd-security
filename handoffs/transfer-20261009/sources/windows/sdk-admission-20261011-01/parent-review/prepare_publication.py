"""Copy exact reviewed plain files; never modify producer sources or receipts."""
import hashlib
import json
import shutil
from pathlib import Path

J=Path(__file__).resolve().parent
P=J/'packet01'
G=J.parent.parent/'shared-build-handoff'
D=G/'handoffs/transfer-20261009/sources/windows/sdk-admission-20261011-01'
assert not D.exists()
D.mkdir(parents=True)
def copy(source,relative):
    dest=D/relative
    dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,dest)
for path in sorted(P.rglob('*')):
    if path.is_file() and path.name!='events.jsonl':
        assert path.suffix not in ['.olean','.ilean','.ir','.stdout','.stderr']
        copy(path,path.relative_to(P))
for name in ['audit_endpoint.py','audit-result01.json','verify_sources.py','generator-review01.json',
             'sdk-source-review01.json','import-review01.json','runner-review01.json',
             'endpoint-review.md','prepare_publication.py','transport-verification01.json']:
    copy(J/name,Path('parent-review')/name)
V=J.parent/'native-crate-source-review01'
for path in sorted(V.iterdir()):
    if path.is_file():copy(path,Path('parent-review/locked-source-comparison')/path.name)
(D/'README.md').write_text('Seven reviewed mathematical SDK admission/group source-model modules and98 complete reports for exact runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for scope and residual native obligations. Full Transfer remains OPEN. No objects, caches, toolchains, raw compiler logs or composed runtime workspaces are published. Producer manifest event-log entries are identity references only; event logs are omitted from the repository payload.\n')
records=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
         for p in sorted(D.rglob('*')) if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps({'kind':'Exact reviewed source/evidence publication; parent did not replay Lean',
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','files':records,'full_transfer':'OPEN'},indent=2)+'\n')
result={'path':str(D),'files':len(records)+1,'bytes':sum(p.stat().st_size for p in D.rglob('*') if p.is_file())}
(J/'publication-payload01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
