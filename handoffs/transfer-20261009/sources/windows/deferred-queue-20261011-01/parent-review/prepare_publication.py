"""Publish exact reviewed sources and receipts; exclude objects and raw logs."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;P=J/'packet01';G=J.parent.parent/'shared-build-handoff'
D=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01'
assert not D.exists();D.mkdir(parents=True)
review=json.loads((J/'endpoint-audit-review01.json').read_bytes())
def copy(src,relative):
 target=D/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
for p in sorted(P.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(P)
 if p.name in ['events.jsonl','compiler-output.txt','fresh-17-complete-declarations.txt','inherited-12-complete-declarations.txt']:continue
 if str(rel).startswith('rejected/') and p.name=='source.lean':
  b=p.read_bytes();target=D/(str(rel)+'.json');target.parent.mkdir(parents=True,exist_ok=True)
  target.write_text(json.dumps({'kind':'Lossless original rejected source, not qualified','original_archive_path':str(rel),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'content_utf8':b.decode()},indent=2)+'\n')
 else:copy(p,rel)
for n in ['verify_endpoint.py','endpoint-audit-review01.json','verify_successor_source.py','successor-source-review01.json','endpoint-review.md','prepare_publication.py','transport-verification01.json']:
 copy(J/n,Path('parent-review')/n)
(D/'README.md').write_text('One new queue model with17 complete reports and one unchanged cache model with12 retained reports, pinned to clean runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for exact scope and remaining implementation/recovery obligations. Full Transfer remains OPEN. Original raw diagnostic and event records are retained outside Git and referenced by exact hashes. No compiler objects, logs, caches or toolchains are published.\n')
for field,name in [('fresh_declarations','fresh-17.json'),('inherited_declarations','inherited-12.json')]:
 target=D/'proof-audits'/name;target.parent.mkdir(exist_ok=True)
 target.write_text(json.dumps({'kind':'Structured complete original declaration output; parent verifies full raw report hashes','audits':review[field]},indent=2)+'\n')
records=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(D.rglob('*')) if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps({'kind':'Exact scoped source/evidence publication; no parent compiler or native replay','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','files':records,'fresh_reports':17,'retained_reports':12,'full_transfer':'OPEN'},indent=2)+'\n')
result={'path':str(D),'files':len(records)+1,'bytes':sum(p.stat().st_size for p in D.rglob('*') if p.is_file())}
(J/'publication-payload01.json').write_text(json.dumps(result,indent=2)+'\n')
hand=[];generated=[]
for p in sorted(D.rglob('*')):
 if p.is_file():
  rel=p.relative_to(D);dest=str(p.relative_to(G))
  (hand if rel.as_posix() in ['source/ShielddSecurity/TransferDeferredQueueSourceModel01.lean','parent-review/verify_endpoint.py','parent-review/verify_successor_source.py','parent-review/prepare_publication.py','parent-review/endpoint-review.md','README.md'] else generated).append(dest)
for name,paths in [('handwritten-pathspec01.nul',hand),('generated-pathspec01.nul',generated)]:
 (J/name).write_bytes(b'\0'.join(s.encode() for s in paths)+b'\0')
print(json.dumps(result))
