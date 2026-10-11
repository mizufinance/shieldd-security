"""Supply explicit list argument to core map identity theorem."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-canonical-word-pending-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
source=(old/'handwritten/TransferCanonicalWordPending01.lean').read_text()
assert source.count('_ = keys := List.map_id')==1
source=source.replace('_ = keys := List.map_id','_ = keys := List.map_id keys')
(ROOT/'handwritten/TransferCanonicalWordPending01.lean').write_text(source)
s=(old/'prepare.py').read_text().replace('transfer-canonical-word-pending-owned-floor-20261011-01','transfer-canonical-word-pending-owned-floor-20261011-02')
s=s.replace("plan['artifact_policy']","failedWord=DIAG/'transfer-canonical-word-pending-20261011-01'\nplan['pins'] += [pin(failedWord/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordPending01.lean','project/ShielddSecurity/TransferCanonicalWordPending01.lean','runs/01-TransferCanonicalWordPending01/stdout.txt']]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':8,'failed_attempts_preserved':1,'failed_credit':0,'guards_unchanged':True})
