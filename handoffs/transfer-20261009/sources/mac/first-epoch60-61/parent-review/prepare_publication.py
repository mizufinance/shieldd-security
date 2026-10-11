"""Publish exact reviewed epoch sources and provenance without caches/logs."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent.parent;G=W/'shared-build-handoff';P=W/'mac-first-epoch60-61-kernel-result01';D=G/'handoffs/transfer-20261009/sources/mac/first-epoch60-61'
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
for name in ['mac-first-epoch-range60-source02','mac-first-epoch-nonzero61-source04']:
 for p in (W/name).iterdir():
  if p.is_file():copy(p,Path('maintained')/name/p.name)
for root in sorted({Path(m['receipt']['path']).parents[2]for m in mods}):
 for n in ['config01.json','overlay-manifest01.json','maintained-inventory01.json','maintained/guard.py','maintained/prepare.py']:copy(root/n,Path('execution-context')/root.name/n)
a=json.loads((J/'import-guard-review01.json').read_bytes())['custom_associations']['CapturedArithmetic45B0000']
copy(a['source']['path'],'inherited-support/ShielddSecurity/CapturedArithmetic45B0000.lean');copy(a['receipt']['path'],'inherited-support/receipt01.json')
# Retain selected DATA and original maintained recipe; whole arithmetic generation/replay is a separate operation.
r=W/'mac-full-arithmetic45-source01'
for n in ['generate.py','extract.py','qualification01.json','generation01.json','plan01.json','protected-history01.json']:copy(r/n,Path('inherited-support/maintained')/n)
copy(r/'data/block-0000.json.zlib','data/arithmetic-block-0000.json.zlib');copy(W/'mac-assertion-provider50-source01/data/block-0000.json.zlib','data/assertion-block-0000.json.zlib');copy(W/'mac-arithmetic-coefficients39-source01/coefficients01.json','data/coefficients01.json');copy(W/'mac-assertion-provider50-source01/extra-coefficients01.json','data/extra-coefficients01.json')
f=json.loads((P/'failures01.json').read_bytes())
for i,e in enumerate(f['kernel']):copy(e['receipt']['path'],Path('failed-receipts')/(str(i)+'.json'))
for i,e in enumerate(f['source_predecessors']):
 for rec in e['files']:
  p=Path(rec['path']);n=Path('failed-source-history')/str(i)/p.name
  if p.suffix=='.lean':encoded(p,str(n)+'.json')
  else:copy(p,n)
for n in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','verify_sources_history.py','source-history-review01.json','inherited-arithmeticB0000-audit-review01.json','endpoint-review.md','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
(D/'README.md').write_text('Two newly qualified epoch modules/42 complete reports for exact runtime844389ee069e1fb2e576708842d0b389b4d9a44a; retained arithmeticB0000 support has10 earlier reports, not a fresh replay. See parent-review/endpoint-review.md. Historical rejected Lean sources are losslessly JSON-encoded. Selected DATA and original recipe references remain intact; complete arithmetic generation and portable full replay remain separate. No Transfer certification.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Reviewed first epoch source/evidence publication',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',files=records,full_transfer='OPEN'),indent=2)+'\n')
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[n for n in files if n.endswith(('.py','.md'))];evidence=[n for n in files if n not in hand]
for n,v in [('pathspecs.txt',files),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]: (J/n).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(files),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence));(J/'publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
