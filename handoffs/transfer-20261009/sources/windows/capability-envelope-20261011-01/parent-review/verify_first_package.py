"""Selected import-pool, first-package root, plan and execution association checks."""
import hashlib,json
from pathlib import Path,PureWindowsPath
J=Path(__file__).resolve().parent;P=J/'packet01'
pools={}
for p in (P/'owned-import-context').glob('*composition-review.json'):
 blob=p.read_bytes();pools[hashlib.sha256(blob).hexdigest()]=(p,json.loads(blob))
baseline={x['module']:x['signature'] for x in json.loads((J.parent/'windows-capability-rows-review01/import-review01.json').read_bytes())['associations']}
audits={x['module']:x for x in json.loads((J/'audit-result01.json').read_bytes())['modules']}
audits={**{x['module']:x for x in json.loads((J.parent/'windows-capability-rows-review01/audit-result01.json').read_bytes())['modules']},**audits}
phase_reports=[]
for phase in json.loads((P/'receipts/qualified-phases.json').read_bytes()):
 task=phase['task'];q=P/'execution-context'/task
 blob=(q/'plan.json').read_bytes();assert len(blob)==phase['plan']['bytes'] and hashlib.sha256(blob).hexdigest()==phase['plan']['sha256']
 plan=json.loads(blob);pool_path,pool=pools[plan['owned_import_pool']['sha256']]
 selected=pool['selected'];assert len(selected)==pool['objects']
 copies=[x['copy'] for x in selected];assert plan['owned_imports']==copies
 first_root=PureWindowsPath(plan['lean_path'][0])
 for x in selected:
  assert PureWindowsPath(x['copy']['path'])==first_root/'ShielddSecurity'/(x['module']+'.olean')
  sig=[x['source']['sha256'],x['source']['bytes'],x['object']['sha256'],x['object']['bytes']]
  if x['module'] in baseline:assert sig==baseline[x['module']]
  else:
   a=audits[x['module']];assert x['source']['sha256']==a['source_sha256']
   objects=[o for o in a['receipt']['objects'] if PureWindowsPath(o['path']).name==x['module']+'.olean'];assert len(objects)==1
   assert objects[0]['sha256']==x['object']['sha256'] and objects[0]['bytes']==x['object']['bytes']
 events=[json.loads(line) for line in (q/'events.jsonl').read_text().splitlines()]
 passed=[e for e in events if e['event']=='attempt_finished' and e['result']['status']=='passed']
 assert len(passed)==1 and passed[0]['module'] in audits
 result=passed[0]['result'];assert result==audits[passed[0]['module']]['receipt']
 for target in plan['targets']:
  if target['module']==passed[0]['module']:
   source=(P/'handwritten-source/ShielddSecurity'/(target['module']+'.lean')).read_bytes()
   assert hashlib.sha256(source).hexdigest()==target['source']['sha256']
 phase_reports.append(dict(task=task,selected_pool=str(pool_path.relative_to(P)),objects=len(selected),first_package_root=str(first_root)))
(J/'first-package-review01.json').write_text(json.dumps(dict(kind='EXACT_PLAN_AND_FIRST_PACKAGE_SOURCE_OBJECT_ASSOCIATION',phases=phase_reports,parent_replay=False,full_transfer='OPEN'),indent=2)+'\n')
print(json.dumps(phase_reports))

