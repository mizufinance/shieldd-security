"""Refresh unchanged manager source against corrected FeeFunding ancestor."""
import hashlib
import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-note-manager-source-20261011-02'
ANCESTOR = ROOT.parent / 'transfer-raw-effects-source-20261011-04'
assert not (ROOT / 'plan.json').exists()
for folder, count in [(OLD, 13), (ANCESTOR, 27)]:
    events = [json.loads(s) for s in (folder / 'events.jsonl').read_text().splitlines()]
    assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
    assert len(events[-1]['result']['audits']) == count
target = ROOT / 'handwritten/TransferNoteManagerSource01.lean'
target.parent.mkdir(exist_ok=False)
shutil.copyfile(OLD / 'handwritten/TransferNoteManagerSource01.lean', target)
producer = (OLD / 'prepare.py').read_text()
producer = producer.replace('transfer-raw-effects-source-20261011-03', 'transfer-raw-effects-source-20261011-04')
producer = producer.replace('transfer-note-manager-owned-floor-20261011-02', 'transfer-note-manager-owned-floor-20261011-03')
producer = producer.replace('Fresh 02 parenthesizes one multiline record-field expression after original parser rejection. Definitions, theorem contracts, guards and audits unchanged. Failed 01 preserved with zero credit.',
    'Fresh 03 replays byte-identical successful02 manager source with the qualified raw04 ancestor whose false-context declaration names are corrected to FeeFunding. No manager definitions, contracts, source bytes, guards or audits changed. Qualified02 and rejected01 remain preserved.')
(ROOT / 'prepare.py').write_text(producer)
assert target.read_bytes() == (OLD / 'handwritten/TransferNoteManagerSource01.lean').read_bytes()
print(json.dumps({'source_byte_identical': True, 'source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
    'fresh_reports': 13, 'refreshed_ancestor': 'raw04 FeeFunding names', 'native_credit': 0}))
