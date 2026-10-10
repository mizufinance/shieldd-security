"""Prepare the actual no16 join only after witness02 passes, owning odd-image imports."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-concrete-eight-witness-20261010-02'
recipe = (OLD / 'prepare.py').read_text()
recipe = recipe.replace("PRIOR = DIAG / 'transfer-concrete-eight-data-20261010-01'", "PRIOR = DIAG / 'transfer-concrete-eight-witness-20261010-02'")
recipe = recipe.replace("source = ROOT / 'handwritten/ConcreteEightTorsionWitness01.lean'", "source = ROOT / 'handwritten/ConcreteNoSixteen01.lean'")
recipe = recipe.replace('len(names) == 11', 'len(names) == 7')
needle = "originals = plan['owned_imports'] + done[0]['result']['objects']"
replacement = """originals = plan['owned_imports'] + done[0]['result']['objects']
odd = DIAG / 'transfer-torsion-odd-image-20261010-03'
odd_plan = json.loads((odd / 'plan.json').read_text())
odd_done = [json.loads(x) for x in (odd / 'events.jsonl').read_text().splitlines() if json.loads(x)['event'] == 'attempt_finished']
assert len(odd_done) == len(odd_plan['targets']) == 1 and odd_done[0]['result']['status'] == 'passed'
existing = {Path(r['path']).name: r for r in originals}
for r in odd_plan['owned_imports'] + odd_done[0]['result']['objects']:
    assert pin(r['path']) == r
    name = Path(r['path']).name
    if name in existing:
        assert existing[name]['bytes'] == r['bytes'] and existing[name]['sha256'] == r['sha256']
    else:
        originals.append(r); existing[name] = r
plan['pins'] += [pin(odd / 'plan.json'), pin(odd / 'events.jsonl'), odd_done[0]['result']['stdout']] + odd_plan['pins']
"""
assert recipe.count(needle) == 1
recipe = recipe.replace(needle, replacement)
recipe = recipe.replace("pin(PRIOR / 'generate.py'), pin(PRIOR / 'generation-review.json'),", "pin(PRIOR / 'prepare_recipe.py'),")
recipe = recipe.replace('ACTUAL_ORDER_EIGHT_WITNESS_AND_EXHAUSTIVE_EIGHT_KERNEL', 'ACTUAL_NO_ORDER_SIXTEEN_AND_ODD_EIGHT_IMAGE')
start = recipe.index("plan['scope'] =")
end = recipe.index("(ROOT / 'plan.json')", start)
recipe = recipe[:start] + """plan['scope'] = 'Every actual order-eight point is one of the four odd witness multiples. Nonsquare first/third coordinates exclude halves, hence actual order sixteen. Cauchy implies the actual eight-multiplication image has odd cardinality. Base-order/cardinality, native and full Transfer remain open.'
plan['repairs'] = 'New handwritten actual exhaustive-torsion/nonsquare/Cauchy join, all owned import objects explicitly copied; inherited exact complete point floor and finite guards.'
""" + recipe[end:]
(ROOT / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(ROOT / 'prepare.py')
