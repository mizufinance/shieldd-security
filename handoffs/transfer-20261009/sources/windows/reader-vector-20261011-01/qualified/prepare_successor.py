"""Preserve vector 02; remove two tactics after simplification already closed the goals."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-nullifier-reader-vector-20261011-02'
assert not (ROOT / 'handwritten').exists() and not (ROOT / 'plan.json').exists()
events = [json.loads(line) for line in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferNullifierReaderVector01.lean').read_text()
repairs = [('simp [contains] at success; contradiction', 'simp [contains] at success'),
    ('simp [contains, observed] at success; contradiction', 'simp [contains, observed] at success')]
for before, after in repairs:
    assert source.count(before) == 1
    source = source.replace(before, after)
handwritten = ROOT / 'handwritten/TransferNullifierReaderVector01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("'Fresh 02 after preserved 01 boolean proof errors: correct boolean negation lemma and simplify gate branches without a nonexistent constant. Executable definitions and theorem contracts unchanged; zero credit for failed predecessor; all guards/audits retained.'", "'Fresh 03 after preserved 01/02 proof-only failures: correct boolean negation lemma, simplify gate branches and remove two tactics after those goals were already closed. Executable definitions and theorem contracts unchanged; rejected attempts zero credit; guards/audits unchanged.'")
(ROOT / 'prepare.py').write_text(recipe)
print(json.dumps({'source': str(handwritten), 'sha256': hashlib.sha256(handwritten.read_bytes()).hexdigest(), 'removed_closed_goal_tactics': 2, 'rejected_credit': 0, 'native_credit': 0}))
