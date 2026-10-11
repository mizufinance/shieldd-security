"""Stage exact reviewed arithmetic sources and lossless bounded provenance."""
from pathlib import Path
import hashlib,json,zlib,shutil,os
J=Path(__file__).parent;W=J.parent.parent;G=W/'shared-build-handoff';P=W/'mac-full-arithmetic45-kernel-result01';D=G/'handoffs/transfer-20261009/sources/mac/full-arithmetic45-52'
assert not D.exists()
FLOOR=2147483648
# Physical write estimate includes filesystem allocation and Git compression slack.
assert shutil.disk_usage(W).free>FLOOR+120*1024*1024
records=[];seen={}
def sha(b):return hashlib.sha256(b).hexdigest()
def emit(b,n):
 p=D/n;p.parent.mkdir(parents=True,exist_ok=True)
 assert shutil.disk_usage(W).free>FLOOR+16*1024*1024
 with p.open('xb')as f:f.write(b)
 assert p.read_bytes()==b
 return dict(path=str(p.relative_to(D)),bytes=len(b),sha256=sha(b))
def copy(p,n,compress=False):
 p=Path(p);b=p.read_bytes();original=dict(path=str(p),bytes=len(b),sha256=sha(b))
 if original['sha256']in seen:return seen[original['sha256']]
 payload=emit(zlib.compress(b,1)if compress else b,n)
 if compress:assert zlib.decompress((D/n).read_bytes())==b
 r=dict(original=original,publication=payload,encoding='zlib'if compress else'identity');records.append(r);seen[original['sha256']]=r;return r
mods=json.loads((P/'qualified-modules01.json').read_bytes());assert len(mods)==610
for e in mods:
 copy(e['source']['path'],Path('source/ShielddSecurity')/(e['name']+'.lean'))
 copy(e['receipt']['path'],Path('receipts')/Path(e['receipt']['path']).name)
for p in sorted(P.iterdir()):
 if p.is_file():copy(p,Path('producer')/p.name)
review_names=['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','verify_sources_history.py','source-history-review01.json','verify_guard_history.py','guard-history-review01.json','prepare_publication.py','endpoint-review.md']
for n in review_names:copy(J/n,Path('parent-review')/n)
pre=J.parent/'full-arithmetic45-pre-review01'
for n in ['replay-review01.json','literal-source-row-review01.json']:
 p=pre/n
 if p.exists():copy(p,Path('parent-DATA-review')/n)
S=W/'mac-full-arithmetic45-source01';q=json.loads((S/'qualification01.json').read_bytes())
for n in ['qualification01.json','generation01.json','extract.py','generate.py']:copy(S/n,Path('recipes/leaves')/n)
for b in q['chunks']:copy(b['data']['path'],Path('data')/Path(b['data']['path']).name)
copy(q['coefficient_store']['path'],Path('data')/'coefficient-store.json')
for version in [1,2]:
 s=W/('mac-full-arithmetic-root52-source0'+str(version))
 for n in ['generate.py','generation01.json']:copy(s/n,Path('recipes')/('root-source0'+str(version))/n)
envelope=json.loads((P/'envelope01.json').read_bytes())
copy(envelope['historical_provenance']['path'],Path('provenance')/'protected-history01.json.zlib',True)
copy(envelope['ledger_observation']['path'],Path('provenance')/'ledger-observation01.json')
imports=json.loads((J/'import-guard-review01.json').read_bytes())
for e in imports['execution_configs']:
 root=Path(e['path']);n=root.name
 copy(root/'config01.json',Path('execution-context')/n/'config01.json.zlib',True)
 for p in sorted((root/'maintained').iterdir()):copy(p,Path('execution-context')/n/'maintained'/p.name)
 for f in ['maintained-inventory01.json','plan01.json']:
  if(root/f).is_file():copy(root/f,Path('execution-context')/n/f)
for e in json.loads((J/'guard-history-review01.json').read_bytes())['guards']:
 copy(W/e['stage']/'maintained/guard.py',Path('guard-history')/e['stage']/'guard.py')
hist=json.loads((P/'attempt-history01.json').read_bytes())
for e in hist['receipts']:copy(e['path'],Path('history-receipts')/(Path(e['path']).parent.parent.parent.name+'-'+Path(e['path']).name+'.zlib'),True)
for e in hist['failed']:copy(e['source']['path'],Path('rejected-source')/(e['module']+'-'+e['source']['sha256'][:12]+'.lean'))
emit((json.dumps(dict(kind='Exact original byte identities and lossless publication mapping; no objects/caches/raw logs',files=records),indent=2)+'\n').encode(),Path('original-byte-map01.json'))
manifest=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
emit((json.dumps(dict(kind='Reviewed complete arithmetic partition, not full Transfer certification',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',modules=610,complete_reports=6012,files=manifest,full_transfer='OPEN'),indent=2)+'\n').encode(),Path('publication-manifest01.json'))
paths=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[p for p in paths if p.endswith(('.py','.md'))];evidence=[p for p in paths if p not in hand]
for n,v in [('pathspecs.txt',paths),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]:(J/n).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
