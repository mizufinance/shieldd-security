"""Retain failed witness01 and remove only tactics after goals already close."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-concrete-eight-witness-20261010-01'
source = (OLD / 'handwritten/ConcreteEightTorsionWitness01.lean').read_text()
before = 'by rw [← mul_nsmul]; rfl'
assert source.count(before) == 2
source = source.replace(before, 'by rw [← mul_nsmul]')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/ConcreteEightTorsionWitness01.lean').write_text(source, encoding='utf-8', newline='\n')
recipe = (OLD / 'prepare.py').read_text()
needle = "plan['kind'] ="
assert recipe.count(needle) == 1
retained = """failed = DIAG / 'transfer-concrete-eight-witness-20261010-01'
history = [pin(failed / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'prepare_recipe.py', 'handwritten/ConcreteEightTorsionWitness01.lean', 'runs/01-ConcreteEightTorsionWitness01/stdout.txt']]
plan['pins'] += history
plan['retained_failed_witness_history'] = history
"""
recipe = recipe.replace(needle, retained + needle, 1)
recipe = recipe.replace('New handwritten actual order/cardinality join.', 'Fresh successor retains failed witness01 with zero proof credit; removes two rfl tactics after rw already closes their goals. New handwritten actual order/cardinality join.')
(ROOT / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(ROOT / 'prepare.py')
