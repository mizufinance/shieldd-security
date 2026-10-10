"""Join every discharged actual curve obligation, retaining exact base order as a premise."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-concrete-no-sixteen-20261010-02'
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("PRIOR = DIAG / 'transfer-concrete-eight-witness-20261010-02'", "PRIOR = DIAG / 'transfer-concrete-no-sixteen-20261010-02'")
recipe = recipe.replace("odd = DIAG / 'transfer-torsion-odd-image-20261010-03'", "odd = DIAG / 'transfer-cardinality-image-20261010-02'")
recipe = recipe.replace("source = ROOT / 'handwritten/ConcreteNoSixteen01.lean'", "source = ROOT / 'handwritten/ConcreteCardinalityJoin01.lean'")
recipe = recipe.replace('len(names) == 7', 'len(names) == 2')
recipe = recipe.replace('ACTUAL_NO_ORDER_SIXTEEN_AND_ODD_EIGHT_IMAGE', 'ACTUAL_CARDINALITY_AND_GLOBAL_EXPONENT_WITH_EXPLICIT_BASE_ORDER')
start = recipe.index("plan['scope'] =")
end = recipe.index("(ROOT / 'plan.json')", start)
recipe = recipe[:start] + """plan['scope'] = 'Actual kernel8cardinality8, no16, oddimage and point bound discharge all curve-side obligations. Given an actual point with exact scalarModulus order, prove actual Nat.card curve.Point=8r and the global8r exponent. Exact runtime-base/order binding is explicitly retained; native/fullTransfer remain open.'
plan['repairs'] = 'New two-lemma handwritten actual cardinality join. No unqualified base-order premise is hidden, no conclusion asserted without it, and same complete external floor and finite guards.'
""" + recipe[end:]
(ROOT / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(ROOT / 'prepare.py')
