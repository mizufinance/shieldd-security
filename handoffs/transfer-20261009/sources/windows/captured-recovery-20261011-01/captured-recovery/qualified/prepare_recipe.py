"""Remove strict unused simp warning; keep both failed whole attempts and unrun 02."""
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-captured-recovery-20261011-03'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferCapturedRecovery01.lean').read_text()
a='cases observed : (TransferBankRecovery.prepare io store.actualRoots committed intent).error <;> simp only [observed]'
b='cases observed : (TransferBankRecovery.prepare io store.actualRoots committed intent).error <;> rfl'
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferCapturedRecovery01.lean').write_text(source)
obj=old/'project/ShielddSecurity/TransferCapturedRecovery01.olean'
metadata={'status':'REJECTED_WHOLE_STRICT_ATTEMPT_UNUSED_WARNING','proof_credit':0,'imported':False,
    'object':{'path':str(obj),'bytes':obj.stat().st_size,'sha256':hashlib.sha256(obj.read_bytes()).hexdigest()},
    'scope':'Compiled with strict unused-simp warning; object never selected/imported and no object bytes in endpoint.'}
(ROOT/'rejected-object-identity.json').write_text(json.dumps(metadata,indent=2,sort_keys=True)+'\n')
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-03'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-04'")
anchor="plan['pins'] += mapping['runtime_sources']"
assert s.count(anchor)==1
s=s.replace(anchor,"rejected_captured03 = DIAG / 'transfer-captured-recovery-20261011-03'\nplan['pins'] += [pin(rejected_captured03 / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean', 'runs/01-TransferCapturedRecovery01/stdout.txt']]\nplan['pins'] += [pin(ROOT / 'rejected-object-identity.json'), pin(rejected_captured03/'project/ShielddSecurity/TransferCapturedRecovery01.olean')]\n"+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Whole failed 01 and warning-only compiled 03 retained with zero credit; prepared 02 UNRUN. Final proof cases already rewrite current error, so redundant simp argument replaced by rfl. All program definitions/theorem contracts and native forward-frame premise unchanged. Rejected 03 object identity preserved, never imported. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':True,'rejected_whole_attempts':2,'rejected_proof_credit':0,'withdrawn02':'UNRUN'})
