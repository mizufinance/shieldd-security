"""Preserve vector 01; repair boolean proof lemma names and branch simplification."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-nullifier-reader-vector-20261011-01'
assert not (ROOT / 'handwritten').exists() and not (ROOT / 'plan.json').exists()
events = [json.loads(line) for line in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferNullifierReaderVector01.lean').read_text()
repairs = [
    ('simp only [contains, Bool.false_eq_true, if_false] at success', 'simp [contains] at success'),
    ('simp only [contains, observed, Bool.true_eq_true, if_true, Option.map_none] at success', 'simp [contains, observed] at success'),
    ('simpa only [contains, observed, Bool.true_eq_true, if_true, Option.map_some] using success', 'simpa [contains, observed] using success'),
    ('Bool.and_eq_true, Bool.not_eq_true] using unspent', "Bool.and_eq_true, Bool.not_eq_true'] using unspent"),
    ('  cases readerGate <;> simp only [contains, failed, Bool.false_eq_true, Bool.true_eq_true,\n    if_false, if_true, Option.map_none]', '  cases readerGate with\n  | false => rfl\n  | true => simp [contains, failed]')]
for before, after in repairs:
    assert source.count(before) == 1, before
    source = source.replace(before, after)
handwritten = ROOT / 'handwritten/TransferNullifierReaderVector01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("'None; first finite source attempt. Existing readback sources unchanged.'", "'Fresh 02 after preserved 01 boolean proof errors: correct boolean negation lemma and simplify gate branches without a nonexistent constant. Executable definitions and theorem contracts unchanged; zero credit for failed predecessor; all guards/audits retained.'")
recipe = recipe.replace("[Path(__file__), runner, handwritten, target, mapping_file]", "[Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target, mapping_file]")
(ROOT / 'prepare.py').write_text(recipe)
print(json.dumps({'source': str(handwritten), 'sha256': hashlib.sha256(handwritten.read_bytes()).hexdigest(), 'proof_repairs': len(repairs), 'rejected_credit': 0, 'native_credit': 0}))
