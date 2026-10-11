"""Parenthesize the multiline record-field expression; preserve failed 01."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-note-manager-source-20261011-01'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferNoteManagerSource01.lean').read_text()
before = '''{child with cache := TransferRawEffectsSource01.putV
      (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]}'''
after = '''{child with cache := (TransferRawEffectsSource01.putV
      (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1])}'''
assert source.count(before) == 1
source = source.replace(before, after)
target = ROOT / 'handwritten/TransferNoteManagerSource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text().replace('transfer-note-manager-owned-floor-20261011-01',
    'transfer-note-manager-owned-floor-20261011-02')
producer = producer.replace('Path(__file__), runner, handwritten', "Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten")
producer = producer.replace('Fresh handwritten callback source; preserved qualified ancestors unchanged.',
    'Fresh 02 parenthesizes one multiline record-field expression after original parser rejection. Definitions, theorem contracts, guards and audits unchanged. Failed 01 preserved with zero credit.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'repair': 'one record field parentheses pair', 'changed_contracts': False, 'rejected_credit': 0}))
