"""Repair actual doubling elaboration without increasing recursion/heartbeat limits."""
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-concrete-point-doubling-20261010-01'
NEW = DIAG / 'transfer-concrete-point-doubling-20261010-02'
NEW.mkdir(exist_ok=False)
(NEW / 'handwritten').mkdir()
source = (OLD / 'handwritten/ConcretePointDoublingSquare01.lean').read_text()
before = '    congr 1 <;> ring'
after = '''    rw [show y - -y = 2 * y by ring]
    apply congrArg (fun numerator : F => numerator / (2 * y))
    ring'''
assert source.count(before) == 1
source = source.replace(before, after)
before = '    exact (nonzero (by simpa using doubled.symm)).elim'
after = '''    have zero : WeierstrassCurve.Affine.Point.mk equation = (0 : curve.Point) :=
      doubled.symm.trans (nsmul_zero 2)
    exact (nonzero zero).elim'''
assert source.count(before) == 1
source = source.replace(before, after)
(NEW / 'handwritten/ConcretePointDoublingSquare01.lean').write_text(source, encoding='utf-8', newline='\n')
recipe = (OLD / 'prepare.py').read_text()
before = "plan['kind'] = 'ACTUAL_POINT_DOUBLING_SQUARE_AND_TWO_NONSQUARE_NO_HALVES'"
after = '''failed = DIAG / 'transfer-concrete-point-doubling-20261010-01'
history = [failed / 'plan.json', failed / 'events.jsonl', failed / 'prepare.py',
    failed / 'handwritten/ConcretePointDoublingSquare01.lean',
    failed / 'runs/01-ConcretePointDoublingSquare01/stdout.txt']
plan['pins'] += [pin(p) for p in history] + [pin(DIAG / 'transfer-concrete-point-doubling-repair-20261010-01/prepare.py')]
plan['retained_failed_doubling_history'] = [pin(p) for p in history]
plan['kind'] = 'ACTUAL_POINT_DOUBLING_SQUARE_AND_TWO_NONSQUARE_NO_HALVES' '''
assert recipe.count(before) == 1
recipe = recipe.replace(before, after)
recipe = recipe.replace("plan['repairs'] = 'New handwritten bridge from the actual Point doubling/slope to the existing symbolic tangent square proof; exact complete owned import closure and unchanged finite guards.'",
    "plan['repairs'] = 'Fresh successor preserves failed01 with zero credit. Replace broad congr descent by an explicit numerator congrArg, and simplify zero-point nsmul by an explicit equality. Same six audits and finite limits; inherits the narrowly repaired temporary-file size monitor.'")
(NEW / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(json.dumps({'created': str(NEW), 'bounded_proof_repairs': 2, 'failed_credit': 0}))
