"""Fresh no16 successor retains both elaboration failures with zero proof credit."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-concrete-no-sixteen-20261010-01'
source = (OLD / 'handwritten/ConcreteNoSixteen01.lean').read_text()
assert source.count('rw [nsmul_neg, doubled, neg_neg]') == 1
assert source.count('apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr') == 1
source = source.replace('rw [nsmul_neg, doubled, neg_neg]', 'rw [neg_nsmul, doubled, neg_neg]')
source = source.replace('apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr', 'apply addOrderOf_dvd_iff_nsmul_eq_zero.mp')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/ConcreteNoSixteen01.lean').write_text(source, encoding='utf-8', newline='\n')
recipe = (OLD / 'prepare.py').read_text()
needle = "plan['kind'] ="
retained = """failed_no16 = DIAG / 'transfer-concrete-no-sixteen-20261010-01'
failed_no16_history = [pin(failed_no16 / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'prepare_recipe.py', 'handwritten/ConcreteNoSixteen01.lean', 'runs/01-ConcreteNoSixteen01/stdout.txt']]
plan['pins'] += failed_no16_history
plan['retained_failed_no16_history'] = failed_no16_history
"""
assert recipe.count(needle) == 1
recipe = recipe.replace(needle, retained + needle, 1)
recipe = recipe.replace('New handwritten actual exhaustive-torsion/nonsquare/Cauchy join,', 'Fresh successor corrects neg_nsmul rewrite name and the mp direction of zero-iff-divisibility; failed01 retained with zero proof credit. New handwritten actual exhaustive-torsion/nonsquare/Cauchy join,')
(ROOT / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(ROOT / 'prepare.py')
