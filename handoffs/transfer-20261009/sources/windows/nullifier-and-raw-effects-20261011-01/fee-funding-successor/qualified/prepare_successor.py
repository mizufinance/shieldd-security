"""Correct two false-branch names to the runtime FeeFunding context."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-raw-effects-source-20261011-03'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
source = (OLD / 'handwritten/TransferRawEffectsSource01.lean').read_text()
source = source.replace('regulated_skips_volume_tail', 'fee_funding_skips_volume_tail')
source = source.replace('regulated_success_retains_reshape_cache', 'fee_funding_success_retains_reshape_cache')
target = ROOT / 'handwritten/TransferRawEffectsSource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text().replace('transfer-raw-effects-owned-floor-20261011-03',
    'transfer-raw-effects-owned-floor-20261011-04')
producer = producer.replace("'crates/core/component/sct/src/component/tree.rs']],",
    "'crates/core/component/sct/src/component/tree.rs', 'crates/core/component/shielded-pool/src/volume_accumulator.rs']],")
producer = producer.replace("'interfaces': [", "'context': 'Runtime TransferProofContext has exactly Ordinary and FeeFunding. The true ordinary flag is Ordinary; false is FeeFunding. Regulated disclosure is not a third context. Earlier 03 packet theorem/prose labels using regulated for false were incorrect; executable definitions and boolean conclusions were correct and unchanged.',\n    'interfaces': [")
producer = producer.replace('Fresh 03 repairs the multiline callback parentheses and explicitly reduces the false regulated branch after failed 02 elaboration. Program checks, callback order, theorem premises/conclusions, guards and audits unchanged. Successful 01 and failed 02 remain preserved; 02 gets zero credit.',
    'Fresh 04 corrects two false-context theorem names from regulated to fee_funding and records exact Ordinary/FeeFunding runtime enum mapping. All program definitions, theorem premises/conclusions, guards and audits unchanged apart from those declaration names. Published/transferred prior03 remains preserved as historical scoped evidence with this labeling correction; failed02 zero credit.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'correction': 'false context is FeeFunding; names and mapping only', 'program_definitions_changed': False,
    'fresh_declarations': 27, 'native_credit': 0}))
