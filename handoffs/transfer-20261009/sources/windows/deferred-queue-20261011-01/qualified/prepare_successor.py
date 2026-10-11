"""Fresh dispatch lemma repair and exact core-only external import closure."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-deferred-queue-model-20261010-02'
EXTERNAL = DIAG / 'transfer-deferred-queue-external-floor-20261010-01'

def pin(p):
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}

assert not (ROOT / 'handwritten').exists() and not EXTERNAL.exists()
assert json.loads((OLD / 'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
text = (OLD / 'handwritten/TransferDeferredQueueSourceModel01.lean').read_text().split('\nset_option pp.all true in\n', 1)[0]
marker = 'theorem index_failure_discards_child_and_consumes_queue'
dispatch = '''theorem post_take_dispatch {O E T X : Type} (put : IndexWriter O E T X)
    (height : Nat) (parent : State O) (queued : List T) (nonempty : queued ≠ []) :
    flush put true true (some height) parent queued =
      match walk put height empty queued with
      | .error error => refused parent [] (.index error)
      | .ok child => ⟨applyCache parent child, [], child.events, none⟩ := by
  unfold flush
  rw [nonempty_test queued nonempty]
  rfl

'''
assert marker in text
text = text.replace(marker, dispatch + marker, 1)
for result in ['failed', 'success']:
    old_body = '  unfold flush\n  rw [nonempty_test queued nonempty, ' + result + ']\n  rfl\n'
    assert old_body in text
    text = text.replace(old_body, '  rw [post_take_dispatch put height parent queued nonempty, ' + result + ']\n', 1)
names = ['ShielddSecurity.TransferDeferredQueueSourceModel01.' + n
    for n in re.findall(r'^(?:inductive|structure|abbrev|def|theorem) ([A-Za-z0-9_]+)', text, re.M)]
assert len(names) == 17
for name in names:
    text += '\nset_option pp.all true in\n#check @' + name + '\n#print axioms ' + name + '\n'
source = ROOT / 'handwritten/TransferDeferredQueueSourceModel01.lean'
source.parent.mkdir()
source.write_bytes(text.encode())
old_plan = json.loads((OLD / 'plan.json').read_bytes())
full = Path(old_plan['external_floor']['path'])
assert pin(full) == {k: old_plan['external_floor'][k] for k in ['path', 'bytes', 'sha256']}
floor = json.loads(full.read_bytes())
assert floor['admission_ready'] and not floor['gaps']
seen = set()
todo = ['Lean', 'Init']
while todo:
    name = todo.pop()
    if name in seen:
        continue
    assert name in floor['modules']
    seen.add(name)
    entry = floor['modules'][name]
    todo.extend(entry['imports'])
    if entry['implicit_Init']:
        todo.append('Init')
assert len(seen) == 2141 and not any(n.startswith('Mathlib') for n in seen)
records = {r['path']: r for n in seen for r in [floor['modules'][n]['source'], *floor['modules'][n]['objects']]}
external = {
    'admission_ready': True, 'gaps': [], 'kind': 'EXACT_RETAINED_CORE_ONLY_TRANSITIVE_SUBCLOSURE',
    'root_modules': ['Lean', 'Init'], 'modules': {n: floor['modules'][n] for n in sorted(seen)},
    'immutable_files': [records[p] for p in sorted(records)],
    'predecessor_floor': pin(full), 'recipe': pin(Path(__file__)),
    'scope': 'Exact unchanged source/object/complete direct-import records selected by transitive closure from the already qualified external floor. Core-only closure for the retained StateDelta import Lean plus implicit Init. No replay, object edits, omitted reachable modules or physical guard changes.',
}
EXTERNAL.mkdir()
external_file = EXTERNAL / 'external-floor.json'
external_file.write_bytes((json.dumps(external, sort_keys=True, separators=(',', ':')) + '\n').encode())
prepare = (OLD / 'prepare.py').read_text()
prepare = prepare.replace('transfer-deferred-queue-owned-floor-20261010-02', 'transfer-deferred-queue-owned-floor-20261010-03')
prepare = prepare.replace('== 16', '== 17').replace("'fresh_audits': 16", "'fresh_audits': 17")
prepare = prepare.replace('Sixteen new public declaration audits', 'Seventeen new public declaration audits')
needle = "plan = json.loads((PRIOR / 'plan.json').read_bytes())"
assert needle in prepare
prepare = prepare.replace(needle, needle + "\nplan['external_floor'] = {'admission_ready': True, **pin(DIAG / 'transfer-deferred-queue-external-floor-20261010-01/external-floor.json')}\n")
needle = "plan['pins'] += [plan['lean'], plan['external_floor'], plan['preservation'], pin(destination)]"
prepare = prepare.replace(needle, needle + "\nplan['pins'] += [pin(DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json')]\nplan['pins'] += [pin(DIAG / 'transfer-deferred-queue-model-20261010-02' / n) for n in ['plan.json', 'events.jsonl', 'handwritten/TransferDeferredQueueSourceModel01.lean', 'project/ShielddSecurity/TransferDeferredQueueSourceModel01.lean', 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt']]\n")
prepare = prepare.replace('Fresh proof-body successor: replace unused simp reductions with direct definitional proofs and rewriting. Same definitions, premises, conclusions and finite physical/lint guards. Rejected predecessor retained with zero proof/control credit.',
    'Fresh post-take dispatch lemma exposes the Option height match before rewriting index outcomes. Same flush definitions and existing theorem premises/conclusions; one new reusable lemma. Both rejected predecessors retained at zero credit. Exact reachable core external subclosure; physical/lint guards unchanged.')
(ROOT / 'prepare.py').write_bytes(prepare.encode())
print(json.dumps({'status': 'FRESH_DISPATCH_LEMMA_AND_EXACT_CORE_CLOSURE_PREPARED_UNRUN', 'source': pin(source),
    'external_floor': pin(external_file), 'external_modules': len(seen), 'external_files': len(records),
    'external_bytes': sum(r['bytes'] for r in records.values()), 'proof_credit': 0}))
