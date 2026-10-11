"""Fresh binder/proof-application repair; reject the first attempt at zero credit."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-raw-state-program-20261011-01'
assert not (ROOT / 'plan.json').exists() and not (ROOT / 'prepare.py').exists()
events = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = OLD / 'handwritten/TransferRawStateProgram01.lean'
text = source.read_text()
for before, after in [('prefix', 'earlierCommands'), ('partial', 'failureCache'), ('unit', 'returnedUnit')]:
    text, count = re.subn(r'\b' + before + r'\b', after, text)
    assert count > 0
old_call = 'delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _ _\n'
assert text.count(old_call) == 1
text = text.replace(old_call, 'delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _\n', 1)
target = ROOT / 'handwritten/TransferRawStateProgram01.lean'
target.parent.mkdir(parents=True)
target.write_bytes(text.encode())
recipe = (OLD / 'prepare.py').read_text()
old_description = "plan['source_repairs'] = 'None; first source attempt. Symbolic arbitrary-list recurrence and small reusable composition lemmas; raw errors retain child cache while enclosing delivery suppresses apply.'"
assert recipe.count(old_description) == 1
recipe = recipe.replace(old_description, "plan['source_repairs'] = 'Fresh alpha-renaming of reserved prefix/partial binders and constructor-like unit binder, plus one proof-call arity correction. Same model definitions and theorem premises/conclusions. First rejected attempt retained at zero proof/control credit.'")
needle = "plan['pins'] = list(unique.values())"
assert recipe.count(needle) == 1
addition = """
plan['pins'] += [pin(ROOT.parent / 'transfer-raw-state-program-20261011-01' / name) for name in [
    'prepare.py', 'plan.json', 'events.jsonl', 'handwritten/TransferRawStateProgram01.lean',
    'project/ShielddSecurity/TransferRawStateProgram01.lean', 'runs/01-TransferRawStateProgram01/stdout.txt']]
plan['pins'] += [pin(ROOT / 'prepare_successor.py')]
"""
recipe = recipe.replace(needle, needle + '\n' + addition, 1)
(ROOT / 'prepare.py').write_bytes(recipe.encode())
print(json.dumps({'status': 'FRESH_BINDER_AND_PROOF_APPLICATION_SOURCE_REPAIR_PREPARED',
    'rejected_credit': 0, 'new_source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(), 'model_or_theorem_contract_changes': 0}))
