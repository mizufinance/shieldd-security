"""Prepare one handwritten witness module from the passed numeric certificates."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-concrete-eight-data-20261010-01'
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("PRIOR = DIAG / 'transfer-concrete-point-coordinate-20261010-01'",
    "PRIOR = DIAG / 'transfer-concrete-eight-data-20261010-01'")
before = "source = ROOT / 'generated/ConcreteEightTorsionData01.lean'\nreview = json.loads((ROOT / 'generation-review.json').read_text())\nassert review['source'] == pin(source) and review['generator'] == pin(ROOT / 'generate.py')\nassert review['input'] == pin(review['input']['path']) and review['kernel_credit'] == 0"
after = "source = ROOT / 'handwritten/ConcreteEightTorsionWitness01.lean'"
assert recipe.count(before) == 1
recipe = recipe.replace(before, after).replace('len(names) == 15', 'len(names) == 11')
before = "plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(ROOT / 'generate.py'),\n    pin(ROOT / 'generation-review.json'), review['input'], pin(PRIOR / 'plan.json'),"
after = "plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(ROOT / 'prepare_recipe.py'),\n    pin(PRIOR / 'generate.py'), pin(PRIOR / 'generation-review.json'), pin(PRIOR / 'plan.json'),"
assert recipe.count(before) == 1
recipe = recipe.replace(before, after)
recipe = recipe.replace('KERNEL_CHECKED_ACTUAL_THREE_TORSION_COORDINATE_CERTIFICATES', 'ACTUAL_ORDER_EIGHT_WITNESS_AND_EXHAUSTIVE_EIGHT_KERNEL')
recipe = recipe.replace('Exact field equations for three finite candidates and integer-backed rows for double1=point2, double2=origin, and point1+point2=point3. Coordinates are in the actual certified field. Exact orders/eight-point enumeration/no16/cardinality, native and full Transfer remain open.',
    'Actual coordinate rows imply point1 double=point2, point2 double=origin, point1 triple=point3. Point1 has exact order8. Fin8 multiples inject/surject onto actual kernel8, so its cardinality is exactly8 and every point killed by8 is enumerated. No16, oddimage, base-order/cardinality, native and full Transfer remain open.')
recipe = recipe.replace('Generated finite integer congruences from pinned DATA; kernel decide checks certificate arithmetic, followed by certified-field cast and actual coordinate-row interfaces. No generated source hand edits and same finite replay guards.',
    'New handwritten actual order/cardinality join. Symbolic nsmul and order lemmas plus finite cardinality injection; same exact owned import closure and finite replay safeguards.')
(ROOT / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(str(ROOT / 'prepare.py'))
