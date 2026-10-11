"""Carry successful 01 unchanged, expose source arguments and join delivery."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-raw-effects-source-20261011-01'
assert not (ROOT / 'plan.json').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['status'] == 'passed' and len(events[-1]['result']['audits']) == 23
source = (OLD / 'handwritten/TransferRawEffectsSource01.lean').read_text()
source = source[:source.index('set_option pp.all true in')]
source = source.replace('noteInsert : Delta O E → Nat → Outcome', 'noteInsert : Delta O E → Bool → Nat → Outcome')
source = source.replace('volumeInsert : Delta O E → Outcome', 'volumeInsert : Delta O E → Bool → Outcome')
source = source.replace('def notes {O E X : Type} (backend : Backend O E X) :',
    'def notes {O E X : Type} (backend : Backend O E X) (capturedSourceHasId : Bool) :')
source = source.replace('backend.noteInsert child output', 'backend.noteInsert child capturedSourceHasId output')
source = source.replace('notes backend {child', 'notes backend capturedSourceHasId {child')
source = source.replace('notes backend child (output :: rest)', 'notes backend capturedSourceHasId child (output :: rest)')
source = source.replace('(backend : Backend O E X) (child : Delta O E) (output : Nat) (rest : List Nat)',
    '(backend : Backend O E X) (capturedSourceHasId : Bool) (child : Delta O E) (output : Nat) (rest : List Nat)')
# reshape passes the initially captured source into every output callback.
source = source.replace('| .ok () => notes backend capturedSourceHasId', '| .ok () => notes backend sourceHasId')
source = source.replace('notes backend capturedSourceHasId {child with cache := {updated',
    'notes backend sourceHasId {child with cache := {updated')
# Ordinary tail reacquires source after all note effects, matching runtime order.
source = source.replace('| some _ => next (recordVolume', '| some sourceHasId => next (recordVolume')
source = source.replace('backend.volumeInsert {child with cache := updated}',
    'backend.volumeInsert {child with cache := updated} sourceHasId')
extra = '''
def deliveryApi {O E X T : Type} (api : Api O E T) (backend : Backend O E X)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (exactMatched ordinary : Bool)
    (inputs outputs : List Nat) : Api O E T :=
  {api with execute := fun child => asCache
    (executeTransfer backend wordMax capacity pendingKey entryKey dayKey exactMatched ordinary child inputs outputs)}

theorem regulated_success_retains_reshape_cache {O E X : Type} (backend : Backend O E X)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (child : Delta O E)
    (inputs outputs : List Nat) (middle : Cache O E)
    (reshaped : reshape backend wordMax capacity pendingKey child inputs outputs = ⟨middle, .ok ()⟩) :
    executeTransfer backend wordMax capacity pendingKey entryKey dayKey true false child inputs outputs =
      ⟨middle, .ok ()⟩ := by
  simp only [executeTransfer, ↓reduceIte, reshaped, next, volumeTail]

theorem late_volume_conflict_rejects_delivery {O E X T : Type}
    (api : Api O E T) (backend : Backend O E X) (wordMax capacity pendingKey entryKey dayKey : Nat)
    (inputs outputs : List Nat) (registryMatches exclusive : Bool) (mode : IndexMode)
    (transaction : T) (parent : State O) (queued : List T) (middle : Cache O E) (sourceHasId : Bool)
    (reshaped : reshape backend wordMax capacity pendingKey ⟨parent, empty⟩ inputs outputs = ⟨middle, .ok ()⟩)
    (source : backend.currentSource ⟨parent, middle⟩ = some sourceHasId)
    (spent : backend.volumePresent ⟨parent, middle⟩ = some true) :
    run (deliveryApi api backend wordMax capacity pendingKey entryKey dayKey true true inputs outputs)
      registryMatches exclusive mode transaction parent queued = none := by
  have failed := actual_late_volume_conflict_keeps_earlier_raw_cache backend
    wordMax capacity pendingKey entryKey dayKey ⟨parent, empty⟩ inputs outputs middle sourceHasId reshaped source spent
  cases registryMatches with
  | false => rfl
  | true =>
    cases exclusive with
    | false => rfl
    | true =>
      simp only [run, begin, deliveryApi, ↓reduceIte, Option.bind_some, failed, asCache, Option.bind_none]

theorem late_volume_conflict_preserves_parent_and_queue {O E X T : Type}
    (api : Api O E T) (backend : Backend O E X) (wordMax capacity pendingKey entryKey dayKey : Nat)
    (inputs outputs : List Nat) (registryMatches exclusive : Bool) (mode : IndexMode)
    (transaction : T) (parent : State O) (queued : List T) (middle : Cache O E) (sourceHasId : Bool)
    (reshaped : reshape backend wordMax capacity pendingKey ⟨parent, empty⟩ inputs outputs = ⟨middle, .ok ()⟩)
    (source : backend.currentSource ⟨parent, middle⟩ = some sourceHasId)
    (spent : backend.volumePresent ⟨parent, middle⟩ = some true) :
    finish parent queued
      (run (deliveryApi api backend wordMax capacity pendingKey entryKey dayKey true true inputs outputs)
        registryMatches exclusive mode transaction parent queued) = (parent, queued) := by
  exact delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _
    (late_volume_conflict_rejects_delivery api backend wordMax capacity pendingKey entryKey dayKey
      inputs outputs registryMatches exclusive mode transaction parent queued middle sourceHasId reshaped source spent)
'''
source += extra
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', source, re.M)
assert len(names) == 27
source += '\n' + '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
source += '\n\nend ShielddSecurity.TransferRawEffectsSource01\n'
target = ROOT / 'handwritten/TransferRawEffectsSource01.lean'
target.parent.mkdir(exist_ok=False)
target.write_text(source)
producer = (OLD / 'prepare.py').read_text()
producer = producer.replace('transfer-raw-effects-owned-floor-20261011-01', 'transfer-raw-effects-owned-floor-20261011-02')
producer = producer.replace('len(names) == 23', 'len(names) == 27').replace("'fresh_audits': 23", "'fresh_audits': 27")
producer = producer.replace('Exact validated capability comparison', 'Captured note source and reacquired ordinary volume source are explicit callback arguments; exact validated capability comparison')
producer = producer.replace('ordinary late volume recheck and exact two verifiable marker writes.',
    'ordinary late volume recheck, exact two verifiable marker writes, and derived enclosing delivery rejection/parent-and-queue preservation.')
producer = producer.replace("Path(__file__), runner, handwritten", "Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten")
producer = producer.replace('Fresh handwritten raw effect source, imports exact qualified batch closure; no changes to ancestor evidence.',
    'Fresh 02 exposes captured source callback arguments and composes the actual late-conflict error with enclosing delivery. Successful 01 source/reports preserved unchanged as scoped prior evidence; not re-imported or counted as a fresh ancestor.')
(ROOT / 'prepare.py').write_text(producer)
print(json.dumps({'fresh_declarations': 27, 'preserved_prior_qualified_declarations': 23,
    'prior_plan_sha256': hashlib.sha256((OLD / 'plan.json').read_bytes()).hexdigest(),
    'prior_source_sha256': hashlib.sha256((OLD / 'handwritten/TransferRawEffectsSource01.lean').read_bytes()).hexdigest(),
    'native_credit': 0}))
