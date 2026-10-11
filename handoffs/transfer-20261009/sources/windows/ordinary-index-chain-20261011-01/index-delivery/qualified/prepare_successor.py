"""Repair cache-selection reduction and already-rewritten height equality."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-ordinary-index-delivery-20261011-01'
assert not (ROOT / 'prepare.py').exists()
source = (BASE / 'handwritten/TransferOrdinaryIndexDelivery01.lean').read_text()
before = '    exact ⟨rfl, (Option.some.inj success).symm⟩'
assert source.count(before) == 1
source = source.replace(before, '    exact ⟨rfl, (Option.some.inj (by simpa only [asCache, observed] using success)).symm⟩')
before = '      refine ⟨registry, unique, height, witness, bodySuccess, heightRead, inspected, applied, ?_, ?_⟩'
assert source.count(before) == 1
source = source.replace(before, '      refine ⟨registry, unique, height, witness, bodySuccess, rfl, inspected, applied, ?_, ?_⟩')
handwritten = ROOT / 'handwritten/TransferOrdinaryIndexDelivery01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
prepare = (BASE / 'prepare.py').read_text().replace('transfer-ordinary-index-delivery-owned-floor-20261011-01', 'transfer-ordinary-index-delivery-owned-floor-20261011-02')
prepare = prepare.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
prepare = prepare.replace('Fresh finite source over exact bound-body and index-inspection union; shared cache/raw sources, objects and reports agree. No ancestors replayed, desired result premise or guard/audit relaxation.',
    'Fresh02 reduces asCache using its actual result observation before equality extraction, and closes already-rewritten height equality by rfl. One program definition and five theorem contracts unchanged. Failed01 whole zero credit. Exact shared ancestry, finite proof/physical guards and strict audits unchanged.')
(ROOT / 'prepare.py').write_text(prepare)
print({'fresh_reports': 6, 'definitions_and_contracts_unchanged': True, 'failed01_credit': 0})
