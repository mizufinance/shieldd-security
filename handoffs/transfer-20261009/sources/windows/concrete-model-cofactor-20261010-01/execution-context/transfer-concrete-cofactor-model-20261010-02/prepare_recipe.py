"""Fresh explicit scalar alias conversion; keep the failed predecessor immutable."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-concrete-cofactor-model-20261010-01'
assert hashlib.sha256((PRIOR / 'prepare.py').read_bytes()).hexdigest() == '177e52060faf45c9e7743188680b1e2b5420eb38ac5c0f0533c6676464551a37'
source = PRIOR / 'handwritten/ConcreteCofactorModel01.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '7da3b6732f58d6232a2b56964aff6c467e47a9d0546452c685c224b0245a95b4'
text = source.read_text()
needle = '  rw [← ConcreteClosedCardinality01.base_order]\n'
assert text.count(needle) == 1
text = text.replace(needle, '  change CurveCardinalityWindow01.scalarModulus • ConcreteClosedCardinality01.base = 0\n' + needle)
directory = ROOT / 'handwritten'
directory.mkdir(exist_ok=False)
(directory / source.name).write_text(text, encoding='utf-8', newline='\n')
prepare = (PRIOR / 'prepare.py').read_text()
needle = "plan['pins'] += floor['input_records'] + owned\n"
assert prepare.count(needle) == 1
prepare = prepare.replace(needle, needle + "plan['pins'] += [pin(ROOT / 'prepare_recipe.py')] + [pin(DIAG / 'transfer-concrete-cofactor-model-20261010-01' / name) for name in ['prepare.py', 'plan.json', 'execute_bounded.py', 'review.json', 'events.jsonl', 'handwritten/ConcreteCofactorModel01.lean', 'runs/01-ConcreteCofactorModel01/stdout.txt']]\n")
prepare = prepare.replace("New handwritten join only. No generated Lean/evidence edit, new axiom or semantic control claim.", "Fresh handwritten scalarModulus/Scalar.order definitional conversion before applying the accepted base-order theorem. No conclusion/premise change, generated edit or new axiom. Preserve the predecessor elaboration rejection, with zero proof/control credit.")
ast.parse(prepare)
(ROOT / 'prepare.py').write_text(prepare, encoding='utf-8', newline='\n')
print('Predecessor preparation SHA256 ' + hashlib.sha256((PRIOR / 'prepare.py').read_bytes()).hexdigest())
print('Predecessor handwritten SHA256 ' + hashlib.sha256(source.read_bytes()).hexdigest())
