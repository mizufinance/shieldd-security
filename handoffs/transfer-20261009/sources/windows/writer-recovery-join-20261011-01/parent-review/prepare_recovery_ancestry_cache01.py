"""Select historical BankRecovery associations from exact published root review; no replay."""
from pathlib import Path
import json, hashlib, subprocess
J=Path(__file__).parent;G=J.parent/'shared-build-handoff'
pub=G/'handoffs/transfer-20261009/sources/windows/readback-publication-20261011-01'
P=J/'windows-writer-recovery-join-review01/packet01'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
review=json.loads((pub/'parent-review/endpoint-audit-review01.json').read_bytes())
module=next(x for x in review['modules']if x['module']=='TransferBankRecovery')
reports=[x for x in review['full_declarations']if x['declaration'].startswith('ShielddSecurity.TransferBankRecovery.')]
assert len(reports)==10
for rel,dest in [('plan.json','qualified/plan.json'),('events.jsonl','qualified/events.jsonl'),('execute_bounded.py','qualified/execute_bounded.py'),('prepare.py','qualified/prepare.py'),('review.json','qualified/review.json'),('source-mapping.json','qualified/source-mapping.json'),('project/ShielddSecurity/TransferBankRecovery.lean','source/ShielddSecurity/TransferBankRecovery.lean')]:
 assert (P/'original-BankRecovery'/rel).read_bytes()==(pub/dest).read_bytes(),rel
 assert subprocess.check_output(['git','show','HEAD:'+str((pub/dest).relative_to(G))],cwd=G)==(pub/dest).read_bytes()
pool=json.loads((J/'windows-reviewed-ancestry-pool560-reports56-modules01.json').read_bytes())
assert 'TransferBankRecovery'not in pool['modules']
pool['modules']['TransferBankRecovery']=dict(source=module['source'],object=module['objects'][0],local_reviewed_source=str(pub/'source/ShielddSecurity/TransferBankRecovery.lean'))
for e in reports:
 assert e['declaration']not in pool['reports']
 pool['reports'][e['declaration']]={k:e[k]for k in ['axioms','full_type_sha256']}
pool['additional_original_qualification']=[dict(module='TransferBankRecovery',review=pin(pub/'parent-review/endpoint-audit-review01.json'),plan=pin(pub/'qualified/plan.json'),events=pin(pub/'qualified/events.jsonl'),runner=pin(pub/'qualified/execute_bounded.py'))]
out=J/'windows-reviewed-ancestry-pool570-reports57-modules01.json'
assert not out.exists();out.write_text(json.dumps(pool,indent=2)+'\n')
print(json.dumps({**pin(out),'reports':len(pool['reports']),'modules':len(pool['modules'])}))
