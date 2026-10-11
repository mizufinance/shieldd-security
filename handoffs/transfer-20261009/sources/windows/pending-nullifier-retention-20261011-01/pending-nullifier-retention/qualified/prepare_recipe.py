"""Fresh proof-only explicit volume adapter and continuation successor."""
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-pending-nullifier-retention-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-pending-nullifier-retention-owned-floor-20261011-01','transfer-pending-nullifier-retention-owned-floor-20261011-02')
s=s.replace("pin(ROOT / 'prepare-rejected-source-association.py')", "pin(DIAG / 'transfer-pending-nullifier-retention-20261011-01/prepare-rejected-source-association.py')")
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""rejected_retention = DIAG / 'transfer-pending-nullifier-retention-20261011-01'
plan['pins'] += [pin(rejected_retention / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingNullifierRetention01.lean',
    'project/ShielddSecurity/TransferPendingNullifierRetention01.lean', 'runs/01-TransferPendingNullifierRetention01/stdout.txt']]
"""+needle)
s=s.replace('Fresh finite symbolic object-footprint/body/index retention composition for both contexts/every index mode; qualified ancestors and guards unchanged.', 'Proof-only successor parenthesizes the note-cache continuation and explicitly reduces the source-preserving volume adapter before case analysis. All eleven contracts and guards unchanged; failed predecessor and preparation refusal preserved with zero credit.')
(ROOT/'prepare.py').write_text(s)
original=(PRIOR/'handwritten/TransferPendingNullifierRetention01.lean').read_text()
lean=original
before='      have later := ih {child with cache := TransferRawEffectsSource01.emit\n        (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)\n          pendingKey child output source).cache (raw.noteEvent output)}'
after=before.replace('cache := TransferRawEffectsSource01.emit','cache := (TransferRawEffectsSource01.emit').replace('(raw.noteEvent output)}','(raw.noteEvent output))}')
assert lean.count(before)==1
lean=lean.replace(before,after)
start=lean.index('theorem ordinary_volume_tail_any_return_frames_other_object')
proof=lean.index(' := by\n',start)+len(' := by\n')
end=lean.index('\ntheorem context_tail_any_return_frames_other_object',proof)
replacement="""  change (match raw.currentSource child with
    | none => (⟨child.cache, .error .source⟩ : Outcome O E (TransferRawEffectsSource01.EffectError (TransferSctInsertionSource01.Error X)))
    | some sourceHasId => next (TransferRawEffectsSource01.recordVolume raw entryKey dayKey child)
        (fun updated => TransferRawEffectsSource01.liftCallback
          (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
            pendingKey {child with cache := updated} payload sourceHasId))).cache.objects other = child.cache.objects other
  cases source : raw.currentSource child with
  | none => rfl
  | some sourceHasId =>
    have earlier := record_volume_any_return_preserves_objects raw entryKey dayKey child
    cases recorded : (TransferRawEffectsSource01.recordVolume raw entryKey dayKey child).result with
    | error error =>
      simpa only [next, recorded] using congrFun earlier other
    | ok returnedUnit =>
      cases returnedUnit
      have later := manager_any_return_frames_other_object manager sct treeKey pendingKey other
        {child with cache := (TransferRawEffectsSource01.recordVolume raw entryKey dayKey child).cache}
        payload sourceHasId notTree notPending
      simpa only [next, recorded, TransferRawEffectsSource01.liftCallback] using later.trans (congrFun earlier other)
"""
lean=lean[:proof]+replacement+lean[end:]
def contracts(text):
    return {m.group(1):m.group(0).split(' :=',1)[0] for m in re.finditer(r'^theorem (\w+)[\s\S]*?(?=\ntheorem|\nset_option pp.all|\Z)',text,re.M)}
assert contracts(lean)==contracts(original) and len(contracts(lean))==11
assert not re.search(r'^\+',lean,re.M)
f=ROOT/'handwritten/TransferPendingNullifierRetention01.lean'; f.parent.mkdir()
f.write_bytes(lean.encode())
print({'fresh_audits':11,'rejected_credit':0,'all_eleven_contracts_unchanged':True})
