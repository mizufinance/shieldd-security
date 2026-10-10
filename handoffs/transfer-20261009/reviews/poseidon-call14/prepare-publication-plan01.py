"""Create a finite SOURCE publication selection. No Git writes or Lean runs."""
from pathlib import Path
import json,hashlib
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');P=R/'work/mac-poseidon-call1-plan14';V=P/'parent-final-call14-review01';F=P/'final-two-result06'
B=Path('handoffs/transfer-20261009');D=B/'sources/mac/poseidon-call14';W=B/'reviews/poseidon-call14'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();entries={};destinations=set()
def add(p,dest):
 assert p.is_file() and not p.is_symlink() and p.suffix not in {'.log','.olean','.ir','.ilean','.xz','.pyc','.sqlite'} and not any(x in p.parts for x in ['.lake','__pycache__'])
 assert not dest.is_absolute() and '..' not in dest.parts and str(dest) not in destinations
 destinations.add(str(dest));entries[str(p)]={'destination':dest.as_posix(),'bytes':p.stat().st_size,'sha256':sha(p),'commit_class':'maintained' if p.suffix in {'.py','.md','.ps1'} or p.name.endswith('.lean.txt') else 'generated'}
selection=json.loads((V/'publication-source-replay02/replay-selection01.json').read_bytes())
assert selection['selected_modules']==57 and selection['retained_actual_type_STD_pairs']==398
for name,v in selection['records'].items():
 p=Path(v['selected_path']);assert sha(p)==v['sha256'];add(p,Path('circuits/ShielddSecurity')/p.name)
for stage in ['readiness03','successor-source03','final-two-math-plan06']:
 for p in sorted((P/stage/'maintained').iterdir()):add(p,D/'generators'/stage/'maintained'/p.name)
 inventory=P/stage/('maintained-inventory06.json' if stage=='final-two-math-plan06' else 'maintained-inventory03.json');add(inventory,D/'generators'/stage/inventory.name)
for rel in ['readiness03/compact-input03.json','readiness03/poseidon381-wide.json','successor-source02/compact-input03.json','successor-source02/poseidon381-wide.json','successor-source02/named-topology01.json','successor-source02/probe-imports01.json','final-two-math-plan06/generation-input06.json']:
 p=P/rel;add(p,D/'generator-inputs'/rel)
# Preserve the three earlier generated mathematical inputs outside the canonical module namespace.
math=json.loads((P/'final-two-math-plan06/generation-input06.json').read_bytes())
for name,e in math['inputs'].items():
 p=Path(e['path']);assert sha(p)==e['sha256'];add(p,D/'generator-inputs/historical-math06'/(name+'.lean'))
for p in sorted((P/'successor-source02/accepted-probes').glob('*.lean')):add(p,D/'generator-inputs/accepted-probes'/p.name)
for rel in ['final-result-manifest06.json','append-only-envelope06.json','postseal-guard06.json','publication-scope06.json','final60-observation06.json','ledger-final60.jsonl','accepted-RAW398-type-audits06.json','freeze_final_result06.py']:
 add(F/rel,D/'final-result06'/rel)
for key,e in json.loads((F/'final-result-manifest06.json').read_bytes())['entries'].items():
 if key.startswith('claims/') or (key.startswith('raw-local-only/') and key.endswith('.json')):
  p=Path(e['path']);assert sha(p)==e['sha256'];add(p,D/'final-result06'/key)
# Historical manifests are identity/provenance records; their linked objects and logs remain local.
for folder,name in [('final-two-control-candidate06','control-candidate-manifest06.json'),('containment-repair05/candidate05','candidate-manifest05.json'),('continuation-candidate04','candidate-manifest04.json')]:
 add(P/folder/name,D/'historical-manifests'/name)
for folder,subdir in [('final-two-control-candidate06','maintained'),('final-two-control-candidate06','controller-maintained')]:
 for p in sorted((P/folder/subdir).iterdir()):add(p,D/'actual-finaltwo-control06'/subdir/p.name)
for rel in ['source-inventory06.json','maintained-inventory06.json','controller-inventory06.json','append-only-envelope06.json','postseal-guard06.json','continuation-context06.json']:
 p=P/'final-two-control-candidate06'/rel
 if p.exists():add(p,D/'actual-finaltwo-control06'/rel)
for p in sorted(V.iterdir()):
 if p.is_file() and p.suffix in {'.py','.json','.txt'} and not p.name.startswith(('opus55-final-call14','review-inputs','review-prompt','publication-plan')):
  add(p,W/p.name)
for folder,names in {
'parent-two-math-review06':['opus55-two-math06-review01.json','parent-math06-review-disposition01.json','parent-two-math-inspection06-01.json'],
'parent-finaltwo-control-review06':['opus55-finaltwo-control06-review01.json','opus55-finaltwo-control06-review02.json','opus55-finaltwo-control06-review03.json','parent-inspection06-01.json','config-dispatch06.json','controller-launch-invocation06.json','fresh-before-approval06-01.json']
}.items():
 for name in names:
  p=P/folder/name
  if p.exists():add(p,W/'prior-reviews'/folder/name)
plan={'schema':'call14-finite-publication-selection-source-v1','status':'SOURCE_PREPARED_UNAPPROVED','entries':entries,'selected_canonical_modules':57,'actual_retained_audits':398,'original_ALL_attempts':60,'original_ALL_remaining':0,'source_selected_bytes':sum(e['bytes'] for e in entries.values()),'raw_logs_objects_caches_toolchains_DB_workspaces_excluded':True,'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','canonical_base_sha':'a1962598ad440af95b0237697c7ee6bcc4226fbd','required_actual_final_Opus_review':'PENDING_QUOTA_RESET','new_Lean_runs':0,'final_certification_refresh':False,'full_Transfer':'OPEN','source_reproduction_scope':'All 57 accepted sources freshly reproduced from three retained closed generators. Original historical generation recipes retain local artifact identity prerequisites, including failed58 raw log, which is deliberately not shipped.'}
(V/'publication-plan01.json').open('x').write(json.dumps(plan,indent=2)+'\n')
print(json.dumps({k:v for k,v in plan.items() if k!='entries'}));print('files',len(entries),'maintained',sum(e['commit_class']=='maintained' for e in entries.values()),'generated',sum(e['commit_class']=='generated' for e in entries.values()))

