"""Repair only callback parentheses and regulated boolean proof reduction."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-raw-effects-source-20261011-02'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferRawEffectsSource01.lean').read_text()
before = '''{api with execute := fun child => asCache
    (executeTransfer backend wordMax capacity pendingKey entryKey dayKey exactMatched ordinary child inputs outputs)}'''
after = '''{api with execute := (fun child => asCache
    (executeTransfer backend wordMax capacity pendingKey entryKey dayKey exactMatched ordinary child inputs outputs))}'''
assert source.count(before) == 1
source = source.replace(before, after)
before = 'simp only [executeTransfer, ↓reduceIte, reshaped, next, volumeTail]'
assert source.count(before) == 1
source = source.replace(before, 'simp [executeTransfer, reshaped, next, volumeTail]')
target = ROOT / 'handwritten/TransferRawEffectsSource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text().replace('transfer-raw-effects-owned-floor-20261011-02',
    'transfer-raw-effects-owned-floor-20261011-03')
producer = producer.replace('Fresh 02 exposes captured source callback arguments and composes the actual late-conflict error with enclosing delivery. Successful 01 source/reports preserved unchanged as scoped prior evidence; not re-imported or counted as a fresh ancestor.',
    'Fresh 03 repairs the multiline callback parentheses and explicitly reduces the false regulated branch after failed 02 elaboration. Program checks, callback order, theorem premises/conclusions, guards and audits unchanged. Successful 01 and failed 02 remain preserved; 02 gets zero credit.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'repair': 'parentheses and boolean proof reduction only', 'rejected_attempt_credit': 0,
    'fresh_declarations': 27, 'program_checks_and_contracts_changed': False}))
