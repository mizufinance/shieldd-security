"""Proof binder rename removes strict warning; retain whole rejected attempt."""
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-take-commit-state-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferTakeCommitState01.lean').read_text()
a='''  | ok unit =>
    cases unit'''
b='''  | ok returnedUnit =>
    cases returnedUnit'''
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferTakeCommitState01.lean').write_text(source)
obj=old/'project/ShielddSecurity/TransferTakeCommitState01.olean'
metadata={'status':'REJECTED_WHOLE_STRICT_ATTEMPT_CONSTRUCTOR_NAME_BINDER_WARNING','proof_credit':0,'imported':False,
    'object':{'path':str(obj),'bytes':obj.stat().st_size,'sha256':hashlib.sha256(obj.read_bytes()).hexdigest()},
    'scope':'Compiled with strict constructor-name-as-variable warning; object never selected/imported and no object bytes in endpoint.'}
(ROOT/'rejected-object-identity.json').write_text(json.dumps(metadata,indent=2,sort_keys=True)+'\n')
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-take-commit-state-owned-floor-20261011-01'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-take-commit-state-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']"
assert s.count(anchor)==1
s=s.replace(anchor,"rejected_take = DIAG / 'transfer-take-commit-state-20261011-01'\nplan['pins'] += [pin(rejected_take / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferTakeCommitState01.lean', 'project/ShielddSecurity/TransferTakeCommitState01.lean', 'runs/01-TransferTakeCommitState01/stdout.txt']]\nplan['pins'] += [pin(ROOT / 'rejected-object-identity.json'), pin(rejected_take/'project/ShielddSecurity/TransferTakeCommitState01.olean')]\n"+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Whole warning-only compiled 01 earns zero credit. Only Unit match proof binder renamed unit to returnedUnit; all program definitions/theorem contracts/native ownership interfaces unchanged. Rejected object retained unused. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'proof_binder_only_repair':True,'rejected_proof_credit':0})
