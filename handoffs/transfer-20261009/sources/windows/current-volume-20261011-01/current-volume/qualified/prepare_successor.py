"""Keep reshape observations stable and use a small volume-tail lemma."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-current-volume-source-20261011-01'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferCurrentVolumeSource01.lean').read_text()
source = source[:source.index('set_option pp.all true in')]
helper = '''theorem volume_tail_existing_entry_refuses {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey pendingKey entryKey dayKey : Nat) (child : Delta O E) (bytes : Bytes)
    (present : (applyCache child.parent child.cache).verifiable entryKey = some bytes) :
    asCache (TransferRawEffectsSource01.volumeTail
      (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
      entryKey dayKey true child) = none := by
  cases source : raw.currentSource child with
  | none =>
    simp [TransferRawEffectsSource01.volumeTail, TransferRawSourceFrames01.installNotes,
      TransferNoteManagerSource01.installNotes, withVolumeRead, source, asCache]
  | some sourceHasId =>
    cases readable : available child with
    | false =>
      simp [TransferRawEffectsSource01.volumeTail, TransferRawSourceFrames01.installNotes,
        TransferNoteManagerSource01.installNotes, withVolumeRead, source,
        TransferRawEffectsSource01.recordVolume, readVolume, readable, next, asCache]
    | true =>
      simp [TransferRawEffectsSource01.volumeTail, TransferRawSourceFrames01.installNotes,
        TransferNoteManagerSource01.installNotes, withVolumeRead, source,
        TransferRawEffectsSource01.recordVolume, readVolume, readable, present, next, asCache]

'''
anchor = 'theorem existing_current_volume_excludes_success'
assert source.count(anchor) == 1
source = source.replace(anchor, helper + anchor)
start = source.index('      cases source : raw.currentSource {child with cache :=')
end = source.index('\ndef deliveryApi', start)
source = source[:start] + '''      simp only [executeOrdinary, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next]
      exact volume_tail_existing_entry_refuses raw manager sct available treeKey pendingKey entryKey dayKey
        {child with cache := (TransferRawEffectsSource01.reshape
          (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
          wordMax capacity nullifierKey child inputs outputs).cache} bytes currentPresent
''' + source[end:]
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', source, re.M)
assert len(names) == 9
source += '\n' + '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
source += '\n\nend ShielddSecurity.TransferCurrentVolumeSource01\n'
target = ROOT / 'handwritten/TransferCurrentVolumeSource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text()
producer = producer.replace('transfer-current-volume-owned-floor-20261011-01', 'transfer-current-volume-owned-floor-20261011-02')
producer = producer.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
producer = producer.replace('len(names) == 8', 'len(names) == 9').replace("'fresh_audits': 8", "'fresh_audits': 9")
producer = producer.replace('Fresh current volume read from child-overlay verifiable presence, with distinct read availability. Existing volume precludes any Ordinary raw success and enclosing delivery/parent-queue mutation without successful reshape or desired spent flag premises. All inherited guards and evidence unchanged.',
    'Fresh02 uses a reusable volume-tail refusal lemma before exposing backend definitions, preserving the recorded reshape observations. Four executable definitions and original four theorem contracts unchanged; one reusable theorem added. Failed01 zero credit. All guards, audits and inherited evidence unchanged.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'repair': 'stable observation staging plus small reusable tail lemma', 'fresh_reports': 9,
    'original_programs_and_contracts_changed': False, 'rejected_credit': 0}))
