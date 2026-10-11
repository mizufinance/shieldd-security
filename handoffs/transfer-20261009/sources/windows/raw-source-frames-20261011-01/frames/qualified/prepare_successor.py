"""Repair record-expression parentheses and trivial conjunction reductions."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-raw-source-frames-20261011-01'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferRawSourceFrames01.lean').read_text()
before = '''{child with cache := TransferRawEffectsSource01.emit
        (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
          pendingKey child output source).cache (raw.noteEvent output)}'''
after = '''{child with cache := (TransferRawEffectsSource01.emit
        (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
          pendingKey child output source).cache (raw.noteEvent output))}'''
assert source.count(before) == 1
source = source.replace(before, after)
before = '''{child with cache := TransferRawEffectsSource01.emitSpends raw.spentEvent
          (TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs).cache inputs} outputs'''
after = '''{child with cache := (TransferRawEffectsSource01.emitSpends raw.spentEvent
          (TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs).cache inputs)} outputs'''
assert source.count(before) == 1
source = source.replace(before, after)
start = source.index('theorem sct_insertion_preserves_input_write_domains')
end = source.index('theorem manager_preserves_input_write_domains', start)
part = source[start:end].replace('simp only [', 'simp [')
source = source[:start] + part + source[end:]
start = source.index('theorem nullifier_batch_preserves_input_write_domains')
end = source.index('theorem reshape_preserves_input_write_domains', start)
part = source[start:end].replace('simp only [', 'simp [').replace(', ↓reduceIte', '')
source = source[:start] + part + source[end:]
before = '| none => simp only [TransferRawEffectsSource01.reshape, installNotes, TransferNoteManagerSource01.installNotes, source]'
assert source.count(before) == 1
source = source.replace(before, before.replace('simp only [', 'simp ['))
target = ROOT / 'handwritten/TransferRawSourceFrames01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text()
producer = producer.replace('transfer-raw-source-frames-owned-floor-20261011-01', 'transfer-raw-source-frames-owned-floor-20261011-02')
producer = producer.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
producer = producer.replace('Fresh symbolic recurrence derives V/NV cache frames from actual modeled nullifier/SCT/pending-object primitives, across all returned results. No desired callback-frame premise. Successful getter/immutable clone representation remains scoped; all guards and ancestors unchanged.',
    'Fresh 02 repairs two multiline cache-expression parentheses and closes True-and-True/false-boolean proof reductions after original01 elaboration rejection. All primitive programs, theorem premises/conclusions, source framing choices, guards and audits unchanged. Original01 zero credit.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'repair': 'two record parentheses pairs and proof reductions only',
    'contracts_changed': False, 'rejected_credit': 0, 'fresh_reports': 7}))
