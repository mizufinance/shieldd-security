"""Publish exact reviewed composed hint source and original provenance."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent.parent;G=W/'shared-build-handoff';P=W/'mac-first-epoch-hints62-kernel-result01';D=G/'handoffs/transfer-20261009/sources/mac/first-epoch-hints62'
assert not D.exists();D.mkdir(parents=True)
def copy(p,n):
 p=Path(p);t=D/n;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t);assert p.read_bytes()==t.read_bytes()
def encoded(p,n):
 p=Path(p);b=p.read_bytes();t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_text(json.dumps(dict(original_path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),content_utf8=b.decode()),indent=2)+'\n');assert json.loads(t.read_bytes())['content_utf8'].encode()==b
mods=json.loads((P/'qualified-modules01.json').read_bytes())
for m in mods:
 copy(m['source']['path'],Path('sources/ShielddSecurity')/(m['module']+'.lean'));copy(m['receipt']['path'],Path('receipts')/(m['module']+'.json'))
for p in P.iterdir():
 if p.is_file():copy(p,Path('producer-result')/p.name)
for p in (W/'mac-first-epoch-hints62-source03').iterdir():
 if p.is_file():copy(p,Path('maintained/mac-first-epoch-hints62-source03')/p.name)
for root in sorted({Path(m['receipt']['path']).parents[2]for m in mods}):
 for n in ['config01.json','overlay-manifest01.json','maintained-inventory01.json','maintained/guard.py','maintained/prepare.py']:copy(root/n,Path('execution-context')/root.name/n)
h=json.loads((P/'predecessors01.json').read_bytes());copy(h['failed_receipt']['path'],'failed-receipts/source02.json')
for i,r in enumerate(h['source_only_producers']):
 for rec in json.loads(Path(r['path']).read_bytes()).values():
  p=Path(rec['path']);name=Path('failed-source-history')/str(i)/p.relative_to(Path(r['path']).parent)
  if p.suffix=='.lean':encoded(p,str(name)+'.json')
  else:copy(p,name)
 copy(r['path'],Path('failed-source-history')/str(i)/'producer-manifest01.json')
for n in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','verify_sources_history.py','source-history-review01.json','endpoint-review.md','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
(D/'README.md').write_text('Reviewed composed epoch hint source: one qualified module/15 complete reports for runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for explicit independent premises and remaining full Transfer obligations. Original failed source bytes are losslessly JSON-encoded. Original receipt references remain intact; logs/objects/caches/workspaces are excluded. No certification.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Reviewed composed first epoch hint source/evidence',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',files=records,full_transfer='OPEN'),indent=2)+'\n')
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[n for n in files if n.endswith(('.py','.md'))];evidence=[n for n in files if n not in hand]
for n,v in [('pathspecs.txt',files),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]: (J/n).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(files),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence));(J/'publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
