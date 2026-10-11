"""Preserve inspection 01; use reflexivity for two already case-reduced proof goals."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-index-inspection-20261011-01'
assert not (ROOT / 'handwritten').exists() and not (ROOT / 'plan.json').exists()
events = [json.loads(line) for line in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferIndexInspectionFacts01.lean').read_text()
before = 'exact ⟨countValue, converted, idRead, countRead, decoded, checked⟩'
after = 'exact ⟨countValue, rfl, idRead, rfl, decoded, checked⟩'
assert source.count(before) == 1
source = source.replace(before, after)
handwritten = ROOT / 'handwritten/TransferIndexInspectionFacts01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("'transfer-index-inspection-owned-floor-20261011-01'", "'transfer-index-inspection-owned-floor-20261011-02'")
recipe = recipe.replace("'None; first finite source attempt.'", "'Fresh 02 after preserved 01 rejection: two observation goals already rewritten by cases use reflexivity. Executable definitions, hypotheses and theorem conclusions are byte-identical; no relaxed audits or guards; failed attempt earns zero credit.'")
recipe = recipe.replace("[Path(__file__), runner, handwritten, target, composition_file, mapping_file]", "[Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target, composition_file, mapping_file]")
(ROOT / 'prepare.py').write_text(recipe)
print(json.dumps({'source': str(handwritten), 'sha256': hashlib.sha256(handwritten.read_bytes()).hexdigest(), 'proof_goal_repairs': 2, 'rejected_credit': 0, 'native_credit': 0}))
