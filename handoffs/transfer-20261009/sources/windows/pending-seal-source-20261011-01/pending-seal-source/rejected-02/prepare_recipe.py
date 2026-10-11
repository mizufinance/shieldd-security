"""Fresh source helper rename for reserved Lean seal command; retain failure."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
ORIGINAL=DIAG/'transfer-pending-seal-source-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(ORIGINAL/'handwritten/TransferPendingSealSource01.lean').read_text()
assert len(re.findall(r'\bseal\b',source))>10
source=re.sub(r'\bseal\b','sealOnce',source)
target=ROOT/'handwritten/TransferPendingSealSource01.lean'
target.parent.mkdir(parents=True)
target.write_text(source)
s=(ORIGINAL/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-pending-seal-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-pending-seal-source-owned-floor-20261011-02'")
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""rejected_seal = DIAG / 'transfer-pending-seal-source-20261011-01'
plan['pins'] += [pin(rejected_seal / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingSealSource01.lean',
    'project/ShielddSecurity/TransferPendingSealSource01.lean', 'runs/01-TransferPendingSealSource01/stdout.txt']]
"""+needle)
s=s.replace("plan['source_repairs'] = 'Fresh exact source-order pending enum one-shot freeze/ensure/current-object framing and full whole-request refusal from current sealed state; qualified ancestors and finite physical/audit guards unchanged.'", "plan['source_repairs'] = 'Fresh handwritten source helper renamed from reserved Lean seal command to sealOnce; exactly the identifier token changes, preserving all premises/conclusions. Failed parser predecessor retained with zero proof/control credit; physical/finite/audit guards unchanged.'")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_audits':412,'owned_modules':42,'failed_predecessors':1})
