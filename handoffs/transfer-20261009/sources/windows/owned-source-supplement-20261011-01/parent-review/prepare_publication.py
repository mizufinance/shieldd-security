"""Publish exact source transport and source-only receiver evidence."""
from pathlib import Path
import hashlib,json,shutil
J=Path(__file__).resolve().parent;P=J/'packet01';G=J.parents[2]/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/owned-source-supplement-20261011-01'
assert not D.exists();D.mkdir(parents=True)
def copy(p,n):
 target=D/n;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target);assert target.read_bytes()==p.read_bytes()
for p in sorted(P.rglob('*')):
 if p.is_file():copy(p,p.relative_to(P))
for n in ['verify_source_supplement.py','source-identity-review01.json','transport-verification01.json','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
(D/'README.md').write_text('Exact original bytes of22 retained Windows Lean source variants, matched to the accepted437-module composition pool. This closes the source transport gap; the earlier415 exact sources remain in their accepted packets. No source normalization, fresh kernel replay, merged source selection or Transfer certification is claimed. The five shared Mac/Windows foundation variants still require selection and final replay. Verify with parent-review/verify_source_supplement.py using this packet and the capability-envelope-20261011-01/owned-import-context/composition-review.json file. Toolchain caches, objects and raw logs are excluded. Full Transfer remains OPEN.\n')
records=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps({'kind':'Exact original Lean source supplement; source-only publication','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','files':records,'full_transfer':'OPEN'},indent=2)+'\n')
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());(J/'pathspecs.txt').write_text('\n'.join(files)+'\n')
hand=[n for n in files if n.endswith(('.lean','.py','README.md'))];gen=[n for n in files if n not in hand]
(J/'handwritten-pathspecs.txt').write_text('\n'.join(hand)+'\n');(J/'evidence-pathspecs.txt').write_text('\n'.join(gen)+'\n')
result={'path':str(D),'files':len(files),'bytes':sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),'handwritten_files':len(hand),'evidence_files':len(gen)}
(J/'publication-payload01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
