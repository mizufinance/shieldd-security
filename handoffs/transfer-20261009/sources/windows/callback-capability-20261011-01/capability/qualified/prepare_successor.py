"""Remove a strict simpa style warning without changing any contract."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-capability-source-20261011-01'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferCapabilitySource01.lean').read_text()
before = 'simpa only [equal] using observed'
assert source.count(before) == 1
source = source.replace(before, 'simp only [equal]')
target = ROOT / 'handwritten/TransferCapabilitySource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text()
producer = producer.replace('transfer-capability-owned-floor-20261011-01', 'transfer-capability-owned-floor-20261011-02')
producer = producer.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
producer = producer.replace('Fresh exact capability source on the corrected Ordinary/FeeFunding raw04 closure. Existing source/evidence remains immutable; no extraction success, proof validity or desired exactMatched boolean is assumed by successful binding inversion.',
    'Fresh 02 removes one simpa style warning after strict original01 audit rejection. Definitions, theorem premises/conclusions and all guards/audits unchanged. Original01 is zero credit even though its compiler exited zero.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'repair': 'case-reduced equality uses simp directly', 'contracts_changed': False,
    'strict_warning_rejected_prior_credit': 0, 'native_credit': 0}))
