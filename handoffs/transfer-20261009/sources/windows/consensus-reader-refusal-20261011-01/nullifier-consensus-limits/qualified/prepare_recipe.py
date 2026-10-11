"""Fresh generator qualification repair; retain rejected generated attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-nullifier-consensus-limits-20261011-01/prepare.py').read_text()
s=s.replace('transfer-nullifier-consensus-limits-owned-floor-20261011-01','transfer-nullifier-consensus-limits-owned-floor-20261011-02')
s=s.replace('transfer-nullifier-consensus-limits-regeneration-20261011-01','transfer-nullifier-consensus-limits-regeneration-20261011-02')
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""rejected_consensus = DIAG / 'transfer-nullifier-consensus-limits-20261011-01'
plan['pins'] += [pin(rejected_consensus / n) for n in ['generate.py', 'generation.json', 'prepare_recipe.py', 'prepare.py',
    'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl',
    'generated/TransferNullifierConsensusLimits01.lean', 'project/ShielddSecurity/TransferNullifierConsensusLimits01.lean',
    'runs/01-TransferNullifierConsensusLimits01/stdout.txt']]
failed_regen = DIAG / 'transfer-nullifier-consensus-limits-regeneration-20261011-01'
plan['pins'] += [pin(failed_regen / n) for n in ['generation.json', 'generated/TransferNullifierConsensusLimits01.lean']]
"""+needle)
s=s.replace("plan['source_repairs'] = 'Maintained exact-source consensus limit generation with derived width bound and unchanged qualified whole-delivery premises/conclusions; independent exact regeneration; no hand-edited output; guards unchanged.'", "plan['source_repairs'] = 'Fresh maintained generator qualifies the three original helper names in their defining namespaces and disables autoImplicit for generated declarations. Qualified consensus-capacity contracts otherwise unchanged; failed original generated output/plan/raw reports and regeneration retained with zero credit; guards unchanged.'")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':379,'owned_modules':38,'failed_predecessors':1})
