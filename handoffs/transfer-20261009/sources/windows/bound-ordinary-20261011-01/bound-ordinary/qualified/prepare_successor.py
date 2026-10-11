"""Expose the executable wrapper at one refusal rewrite; retain failed01."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-bound-ordinary-source-20261011-01'
assert not (ROOT / 'prepare.py').exists()
source = (BASE / 'handwritten/TransferBoundOrdinarySource01.lean').read_text()
before = '      rw [TransferCapabilitySource01.exact_rebinding_dispatches_projected_action _ extract inputs outputs'
assert source.count(before) == 1
source = source.replace(before, '      rw [executeBound, TransferCapabilitySource01.exact_rebinding_dispatches_projected_action _ extract inputs outputs')
handwritten = ROOT / 'handwritten/TransferBoundOrdinarySource01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
prepare = (BASE / 'prepare.py').read_text().replace('transfer-bound-ordinary-owned-floor-20261011-01', 'transfer-bound-ordinary-owned-floor-20261011-02')
prepare = prepare.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
prepare = prepare.replace('Fresh finite source; exact common raw source/object/audit ancestry checked across both parent branches. No ancestor replay, guard relaxation or desired raw outcome premise.',
    'Fresh02 unfolds executeBound at one existing-entry refusal rewrite before applying the exact rebinding lemma. Two program definitions and ten theorem contracts unchanged. Failed01 whole zero credit; exact common raw source/object/audit ancestry, guards and strict audits unchanged.')
(ROOT / 'prepare.py').write_text(prepare)
print({'fresh_reports': 12, 'definitions_and_contracts_unchanged': True, 'failed01_credit': 0})
