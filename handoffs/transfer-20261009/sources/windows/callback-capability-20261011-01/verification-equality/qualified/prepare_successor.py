"""Normalize conjunction association in the fieldwise equality proof."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-verification-equality-source-20261011-01'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferVerificationEqualitySource01.lean').read_text()
before = '  simp [itemEq]\n'
assert source.count(before) == 1
source = source.replace(before, '  simp [itemEq, and_assoc]\n')
target = ROOT / 'handwritten/TransferVerificationEqualitySource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text()
producer = producer.replace('transfer-verification-equality-owned-floor-20261011-01',
    'transfer-verification-equality-owned-floor-20261011-02')
producer = producer.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
producer = producer.replace('Fresh explicit family/statement-scalar/serialized-envelope comparison and ensure_binds source model. Complete derived DecidableEq instance is included in the full type/axiom census. All ancestors and guards unchanged; statement-preimage semantics and registry verification remain separate.',
    'Fresh 02 adds conjunction association to the equality proof after original01 elaboration failure. All comparisons, definitions, theorem contracts, guards and complete audits including derived DecidableEq remain unchanged. Original01 is zero credit; statement-preimage semantics and registry verification remain separate.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'repair': 'one conjunction association proof lemma', 'contracts_changed': False,
    'fresh_reports': 13, 'rejected_credit': 0, 'native_credit': 0}))
