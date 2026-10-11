"""Prepare SDK subgroup admission and randomization join; no Lean execution."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'handwritten/SDKSubgroupAdmission01.lean'
body = source.read_text()
assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == 10
audit = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKSubgroupAdmission01.' + name + '\n#print axioms ShielddSecurity.SDKSubgroupAdmission01.' + name for name in names)
source.write_text(body + '\n' + audit + '\n', encoding='utf-8', newline='\n')
text = (ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py').read_text()
text = text.replace('ConcreteSubgroupAdmission01', 'SDKSubgroupAdmission01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01', 'transfer-sdk-admission-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 402", "floor['objects'] == 406")
text = text.replace('assert len(names) == 7', 'assert len(names) == 10')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.SDKJubjubMultiply01', 'ShielddSecurity.ConcreteSubgroupAdmission01']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION', 'SDK_MODULUS_ADMISSION_RANDOMIZATION_COFACTOR_JOIN')
start = text.index("plan['scope'] = ")
end = text.index("plan['source_repairs']", start)
scope = 'Independent SDK source-model curve/modulus admission implies concrete subgroup membership and equivalence to the eight-image relation; joins owned native admission and authorization preimage. SDK five-coordinate randomization with the explicit traced mathematical base admits a complete native cofactor preimage. Ten full type/axiom audits. Primitive Rust byte/field/iterator refinement, SPEND_AUTH equality and full Transfer remain open. No runtime/BMC/control/certification credit.'
text = text[:start] + "plan['scope'] = " + repr(scope) + '\n' + text[end:]
text = text.replace('pin(Path(__file__)), pin(source)', "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-multiply-model-20261010-03' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKJubjubMultiply01.lean']]\nplan['source_repairs'] =")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-admission-model-20261010-01' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKSubgroupAdmission01.lean', 'runs/01-SDKSubgroupAdmission01/stdout.txt']]\nplan['source_repairs'] =")
text = text.replace("pin(ROOT / 'prepare_recipe.py'), pin(source)", "pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'repair_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-admission-model-20261010-02' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKSubgroupAdmission01.lean', 'runs/01-SDKSubgroupAdmission01/stdout.txt']]\nplan['source_repairs'] =")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-admission-model-20261010-03' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKSubgroupAdmission01.lean', 'runs/01-SDKSubgroupAdmission01/stdout.txt']]\nplan['source_repairs'] =")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-admission-model-20261010-04' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKSubgroupAdmission01.lean', 'runs/01-SDKSubgroupAdmission01/stdout.txt']]\nplan['source_repairs'] =")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Ten-audit SDK admission/randomization/cofactor source-model join; physical guards unchanged.')
