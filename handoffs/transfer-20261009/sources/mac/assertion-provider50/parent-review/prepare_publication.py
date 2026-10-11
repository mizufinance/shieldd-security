"""Copy exact reviewed sources/recipes/evidence; omit logs, objects and workspaces."""
from pathlib import Path
import hashlib,json,shutil
J=Path(__file__).resolve().parent;W=J.parent.parent;G=W/'shared-build-handoff';P=W/'mac-assertion-provider50-kernel-result01';PRE=J.parent/'assertion-provider50-pre-review01';D=G/'handoffs/transfer-20261009/sources/mac/assertion-provider50'
assert not D.exists();D.mkdir(parents=True)
def copy(p,n):
 p=Path(p);target=D/n;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target);assert target.read_bytes()==p.read_bytes()
mods=json.loads((P/'qualified-modules01.json').read_bytes())
for n,m in mods.items():
 copy(m['source']['path'],Path('sources/ShielddSecurity')/(n+'.lean'))
 copy(m['receipt']['path'],Path('receipts')/(n+'.json'))
for p in P.iterdir():
 if p.is_file():copy(p,Path('producer-result')/p.name)
for folder in ['mac-assertion-provider50-source01','mac-assertion-root54-source01','mac-assertion-controls56-source01','mac-assertion-links57-source01','mac-assertion-links57-source02']:
 root=W/folder
 for p in root.iterdir():
  if p.is_file():copy(p,Path('maintained')/folder/p.name)
for p in (W/'mac-assertion-provider50-source01/data').iterdir():
 assert p.is_file()and p.name.endswith('.zlib');copy(p,Path('data')/p.name)
copy(W/'mac-arithmetic-coefficients39-source01/coefficients01.json','data/coefficients01.json')
root=W/'mac-assertion-provider50-portable-source01'
for p in root.rglob('*'):
 if p.is_file():copy(p,Path('portable-source')/p.relative_to(root))
for configroot in sorted({Path(m['receipt']['path']).parents[2]for m in mods.values()}):
 for n in ['config01.json','overlay-manifest01.json','maintained/guard.py','maintained/prepare.py']:copy(configroot/n,Path('execution-context')/configroot.name/n)
failed=json.loads((P/'failed-attempts01.json').read_bytes())
for i,v in enumerate(failed):
 prefix=f'{i:02d}-{Path(v["source"]["path"]).stem}'
 copy(v['receipt']['path'],Path('failed-receipts')/(prefix+'.json'))
 b=Path(v['source']['path']).read_bytes();assert len(b)==v['source']['bytes']and hashlib.sha256(b).hexdigest()==v['source']['sha256']
 target=D/'failed-source'/(prefix+'.lean.json');target.parent.mkdir(parents=True,exist_ok=True)
 target.write_text(json.dumps({'original_path':v['source']['path'],'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'content_utf8':b.decode()},indent=2)+'\n');assert json.loads(target.read_bytes())['content_utf8'].encode()==b
for n in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review02.json','verify_sources_history.py','source-history-review01.json','endpoint-review.md','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
b=(J/'guard-delta01.diff').read_bytes()
target=D/'parent-review/guard-delta01.diff.json';target.write_text(json.dumps({'original_path':'guard-delta01.diff','bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'content_utf8':b.decode()},indent=2)+'\n');assert json.loads(target.read_bytes())['content_utf8'].encode()==b
for n in ['capture-replay-review01.json','check_extra_coefficients.py','coefficient-dispatch-review02.json','verify_source_regeneration04.py','source-regeneration-review04.json','verify_literal_rows06.py','literal-source-row-review06.json','review_root54.py','root54-source-review01.json','review_portable_source01.py','portable-source-review01.json','portable-source-replay01.json']:
 copy(PRE/n,Path('parent-review/pre-review')/n)
(D/'README.md').write_text('Reviewed complete indexed assertion/link row provider:100 qualified modules/842 original complete reports for runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for precise scope and remaining full Transfer obligations. Original failed source streams are losslessly JSON-encoded with exact bytes/SHA; failed sources/receipts are excluded from any accepted replay. Original manifests may reference local immutable logs, objects, database or workspaces; these are not repository payloads. Portable leaf generation accepts explicit DATA paths; original historical root/control recipes retain original path spellings. Full generator closure and final scoped replay remain separate. No certification is claimed.\n')
records=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps({'kind':'Reviewed exact assertion provider source/evidence publication','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','files':records,'full_transfer':'OPEN'},indent=2)+'\n')
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[n for n in files if n.endswith(('.py','.md','.diff'))];generated=[n for n in files if n not in hand]
for n,items in [('pathspecs.txt',files),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',generated)]:
 (J/n).write_text('\n'.join(items)+'\n')
result={'path':str(D),'files':len(files),'bytes':sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),'handwritten':len(hand),'generated':len(generated)}
(J/'publication-payload01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
