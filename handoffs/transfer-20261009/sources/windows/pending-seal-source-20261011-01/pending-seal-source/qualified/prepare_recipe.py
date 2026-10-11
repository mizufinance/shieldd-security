"""Fresh proof-only successor; retain both failed source attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PREVIOUS=DIAG/'transfer-pending-seal-source-20261011-02'
assert not (ROOT/'prepare.py').exists()
source=(PREVIOUS/'handwritten/TransferPendingSealSource01.lean').read_text()
needle='  simp only [sealOnce, opened, Bool.false_eq_true, if_false]\n  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩'
assert source.count(needle)==1
source=source.replace(needle,'''  have output : sealOnce encode decode objectKey child =
      ⟨(putObject child objectKey (some (encode (freeze (TransferCurrentPendingReplay01.currentPending decode objectKey child))))).cache, .ok ()⟩ := by
    simp only [sealOnce, opened, Bool.false_eq_true, if_false]
  rw [output]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩''')
target=ROOT/'handwritten/TransferPendingSealSource01.lean'
target.parent.mkdir(parents=True)
target.write_text(source)
s=(PREVIOUS/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-pending-seal-source-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-pending-seal-source-owned-floor-20261011-03'")
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""rejected_seal_second = DIAG / 'transfer-pending-seal-source-20261011-02'
plan['pins'] += [pin(rejected_seal_second / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingSealSource01.lean',
    'project/ShielddSecurity/TransferPendingSealSource01.lean', 'runs/01-TransferPendingSealSource01/stdout.txt']]
"""+needle)
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh proof-only opened-seal frame proof rewrites its derived outcome before constructing conjuncts; all thirteen declarations/contracts unchanged from renamed successor. Both failed parser/reflexive-simp attempts retained with zero credit. Physical/finite/lint/audit guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_audits':412,'owned_modules':42,'failed_predecessors':2})
