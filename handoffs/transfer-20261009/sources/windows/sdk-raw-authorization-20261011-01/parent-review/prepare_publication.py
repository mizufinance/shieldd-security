"""Copy exact reviewed plain files; never modify producer sources or receipts."""
import hashlib
import json
import shutil
from pathlib import Path

J=Path(__file__).resolve().parent
P=J/'packet01'
G=J.parent.parent/'shared-build-handoff'
D=G/'handoffs/transfer-20261009/sources/windows/sdk-raw-authorization-20261011-01'
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
for name in ['audit_endpoint.py','audit-result01.json','verify_sources.py','declaration-inventory01.json',
             'sdk-source-review01.json','import-review01.json','runner-review01.json',
             'endpoint-review.md','prepare_publication.py','transport-verification01.json','runtime-source-review01.json','receiver-packaging-review01.json']:
    copy(J/name,Path('parent-review')/name)
S=J.parent/'windows-coordinate-supplement-review01'
for path in sorted((S/'packet01').rglob('*')):
    if path.is_file() and path.name!='events.jsonl':copy(path,Path('supplement')/path.relative_to(S/'packet01'))
for name in ['verify_supplement.py','supplement-review01.json','transport-verification01.json','receiver-review01.json']:
    copy(S/name,Path('parent-review/supplement')/name)
(D/'README.md').write_text('Reviewed16-source raw SDK/model authorization packet:172 original reports plus one diagnostic supplement for an unchanged public helper;173 public declarations inventoried. Exact runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for explicit global primitive and generator-coordinate premises. Full Transfer remains OPEN. Objects, caches, toolchains, raw compiler and event logs are omitted; producer manifest references preserve their original identities.\n')

records=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
         for p in sorted(D.rglob('*')) if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps({'kind':'Exact reviewed source/evidence publication; parent did not replay Lean',
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','files':records,'full_transfer':'OPEN'},indent=2)+'\n')
result={'path':str(D),'files':len(records)+1,'bytes':sum(p.stat().st_size for p in D.rglob('*') if p.is_file())}
(J/'publication-payload01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
