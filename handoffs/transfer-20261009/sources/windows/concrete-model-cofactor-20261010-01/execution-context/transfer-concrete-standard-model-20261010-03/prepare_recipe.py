"""Fresh successor removes one redundant tactic, retaining the rejected receipt."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-01/prepare.py'
with prior.open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest() == '10181a55d5bff6307bc14283c7bbb37464ebbab9af58cffa1c735f802f0faee5'
text = prior.read_text()
needle = "    text = original.read_text()"
repair = """    text = original.read_text()
    if module == 'EdwardsTorsionAlgebra01':
        needle = '  field_simp [nonzeroX] <;> ring'
        assert text.count(needle) == 1
        text = text.replace(needle, '  field_simp [nonzeroX]')"""
assert text.count(needle) == 1
text = text.replace(needle, repair)
needle = "plan['pins'] += records"
retain = """failed = DIAG / 'transfer-concrete-standard-model-20261010-01'
records += [pin(failed / name) for name in ['prepare.py', 'plan.json', 'review.json',
    'events.jsonl', 'execute_bounded.py', 'runs/01-EdwardsTorsionAlgebra01/stdout.txt']]
records += [pin(p) for p in (failed / 'handwritten').glob('*.lean')]
records += [pin(ROOT / 'prepare_recipe.py')]
plan['pins'] += records"""
assert text.count(needle) == 1
text = text.replace(needle, retain)
text = text.replace("plan['scope'] = 'Replay five maintained handwritten addition modules, full types and standard axioms. No native representation or full Transfer claim.'",
"plan['scope'] = 'Fresh successor replays five maintained handwritten addition modules. EdwardsTorsionAlgebra01 removes one redundant ring after field_simp; rejected warning attempt preserved with zero credit. Full types/standard axioms; native/full Transfer open.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Created fresh finite successor recipe.')
