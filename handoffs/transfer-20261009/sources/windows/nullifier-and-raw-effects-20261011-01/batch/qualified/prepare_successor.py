"""Preserve batch 01; repair min normalization and local proof elaboration only."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-nullifier-batch-source-20261011-01'
assert not (ROOT / 'handwritten').exists() and not (ROOT / 'plan.json').exists()
events = [json.loads(line) for line in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferNullifierBatchSource01.lean').read_text()
repairs = [
    ('  by_cases withinWord : current + requested ≤ wordMax', '  rw [Nat.min_eq_min] at allowed\n  by_cases withinWord : current + requested ≤ wordMax'),
    ('have same : appendPending (backend.pending child) keys = next := Except.ok.inj\n                (by simpa [inspect, unique, sealed, allowed, fresh, observed, unspent] using success)',
     'have same : appendPending (backend.pending child) keys = next := by\n                simpa [inspect, unique, sealed, allowed, fresh, observed, unspent] using success'),
    ('change (backend.pending child).membership key || keys.contains key = true', 'change ((backend.pending child).membership key || keys.contains key) = true'),
    ('have same : (putObject child objectKey (some (backend.encode next))).cache = cache :=\n        congrArg (fun outcome : Outcome O E BatchError => outcome.cache)\n          (by simpa [executeNullify, nonempty, observed] using success)',
     'have same : (putObject child objectKey (some (backend.encode next))).cache = cache := by\n        simpa [executeNullify, nonempty, observed] using success')]
for before, after in repairs:
    assert source.count(before) == 1, before
    source = source.replace(before, after)
handwritten = ROOT / 'handwritten/TransferNullifierBatchSource01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("'transfer-nullifier-batch-owned-floor-20261011-01'", "'transfer-nullifier-batch-owned-floor-20261011-02'")
recipe = recipe.replace("'None; first finite source attempt. Existing imported sources unchanged.'", "'Fresh 02 after preserved 01 proof elaboration failure: normalize Nat.min to its standard instance, let simplification produce the two exact equalities, and parenthesize boolean-or equality. Definitions, premises and theorem conclusions unchanged; rejected attempt zero credit; guards/audits unchanged.'")
recipe = recipe.replace("[Path(__file__), runner, handwritten, target, composition_file, mapping_file]", "[Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target, composition_file, mapping_file]")
(ROOT / 'prepare.py').write_text(recipe)
print(json.dumps({'source': str(handwritten), 'sha256': hashlib.sha256(handwritten.read_bytes()).hexdigest(), 'proof_repairs': len(repairs), 'rejected_credit': 0, 'native_credit': 0}))
