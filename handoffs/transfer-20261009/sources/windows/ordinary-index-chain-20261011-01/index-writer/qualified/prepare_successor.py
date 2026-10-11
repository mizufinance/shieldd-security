"""Preserve failed 01; repair field syntax and local proof elaboration in fresh 02."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-index-writer-model-20261011-01'
assert not (ROOT / 'handwritten').exists() and not (ROOT / 'plan.json').exists()
events = [json.loads(line) for line in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'failed'
source = (OLD / 'handwritten/TransferIndexWriterModel01.lean').read_text()
replacements = [
    ('{api with index := fun height transaction child =>\n    asCache (executeIndex keys codec backend height transaction child)}',
     '{api with index := (fun height transaction child =>\n    asCache (executeIndex keys codec backend height transaction child))}'),
    ('simp only [writeIndex, putNV, if_pos rfl]', 'simp only [writeIndex, putNV, ite_true]'),
    ('exact ⟨witness, observed, same.symm⟩', 'exact ⟨witness, rfl, same.symm⟩'),
    ('  obtain ⟨witness, inspected, same⟩ := successful_index_writes',
     '  change asCache (executeIndex keys codec backend height transaction ⟨parent, cache⟩) = some indexed at observedIndex\n  obtain ⟨witness, inspected, same⟩ := successful_index_writes')]
for before, after in replacements:
    assert source.count(before) == 1
    source = source.replace(before, after)
handwritten = ROOT / 'handwritten/TransferIndexWriterModel01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
recipe = (OLD / 'prepare.py').read_text()
assert recipe.count("'transfer-index-writer-owned-floor-20261011-01'") == 1
recipe = recipe.replace("'transfer-index-writer-owned-floor-20261011-01'", "'transfer-index-writer-owned-floor-20261011-02'")
recipe = recipe.replace("'crates/core/app/src/app/state_key.rs']", "'crates/core/app/src/app/state_key.rs', 'third_party/cnidarium-0.83.0/src/delta.rs', 'third_party/cnidarium-0.83.0/src/cache.rs']")
recipe = recipe.replace("'None; first source attempt with finite reusable primitive/framing/composition lemmas.'", "'Fresh successor after rejected 01: parenthesize record-field lambda, use ite_true, use the case-reduced observation goal and expose the installed callback at its exact type. Intended executable check/write order and all theorem contracts unchanged; original 01 preserved with zero credit.'")
recipe = recipe.replace("[Path(__file__), runner, handwritten, target, composition_file, mapping_file]", "[Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target, composition_file, mapping_file]")
(ROOT / 'prepare.py').write_text(recipe)
print(json.dumps({'fresh_source': str(handwritten), 'bytes': handwritten.stat().st_size,
    'sha256': hashlib.sha256(handwritten.read_bytes()).hexdigest(),
    'rejected_credit': 0, 'source_repairs': len(replacements), 'native_credit': 0}))
