"""Preserve failed Point01; create an independently pinned handwritten successor."""
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-concrete-point-torsion-20261010-01'
NEW = DIAG / 'transfer-concrete-point-torsion-20261010-02'
NEW.mkdir(exist_ok=False)
(NEW / 'handwritten').mkdir()
source = (OLD / 'handwritten/ConcretePointTorsion01.lean').read_text()
before = '  rw [Nat.card_congr curve.pointEquiv, Nat.card_congr finiteSolutionsEquiv.optionCongr]'
after = '''  rw [Nat.card_congr curve.pointEquiv]
  change Nat.card (Option {xy : F × F // curve.Equation xy.1 xy.2}) ≤
    2 * TorsionEulerInteger49.modulus + 1
  rw [Nat.card_congr finiteSolutionsEquiv.optionCongr]'''
assert source.count(before) == 1
source = source.replace(before, after)
before = '  let roots := Finset.univ.filter (fun point : curve.Point => 2 • point = 0)'
after = '''  let roots := Finset.univ.filter (fun point : curve.Point =>
    point ∈ (DoublingKernelBound01.multiply (J := curve.Point) 2).ker)'''
assert source.count(before) == 1
source = source.replace(before, after)
before = '    rcases two_torsion_cases point (Finset.mem_filter.mp present).2 with zero | origin'
after = '''    have killed : 2 • point = 0 := (AddMonoidHom.mem_ker.mp
      (Finset.mem_filter.mp present).2)
    rcases two_torsion_cases point killed with zero | origin'''
assert source.count(before) == 1
source = source.replace(before, after)
(NEW / 'handwritten/ConcretePointTorsion01.lean').write_text(source, encoding='utf-8', newline='\n')
recipe = (OLD / 'prepare.py').read_text()
before = "plan['kind'] = 'ACTUAL_CONCRETE_POINT_BOUND_AND_TWO_TORSION_CLASSIFICATION'"
after = '''failed = DIAG / 'transfer-concrete-point-torsion-20261010-01'
history = [failed / 'plan.json', failed / 'events.jsonl', failed / 'prepare.py',
    failed / 'handwritten/ConcretePointTorsion01.lean',
    failed / 'runs/01-ConcretePointTorsion01/stdout.txt']
plan['pins'] += [pin(p) for p in history] + [pin(DIAG / 'transfer-concrete-point-repair-recipe-20261010-01/prepare.py')]
plan['retained_failed_history'] = [pin(p) for p in history]
plan['kind'] = 'ACTUAL_CONCRETE_POINT_BOUND_AND_TWO_TORSION_CLASSIFICATION' '''
assert recipe.count(before) == 1
recipe = recipe.replace(before, after)
recipe = recipe.replace("plan['repairs'] = 'New handwritten actual Point join with complete exact owned import closure, completed official-cache first package composition and unchanged finite executor limits.'",
    "plan['repairs'] = 'Fresh successor preserving failed Point01 with zero credit. Convert WithZero to Option before cardinality rewrite; count actual hom kernel membership before converting its predicate to the doubling equation. Same 17 audits, exact import closure, first package composition and finite executor limits.'")
(NEW / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(json.dumps({'created': str(NEW), 'handwritten_repairs': 2, 'failed_predecessor_credit': 0}))
