"""Prepare separate concrete arithmetic bridge; no Lean run."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py'
source = ROOT / 'handwritten/SDKJubjubConcrete01.lean'
body = source.read_text()
assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == 2
audit = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKJubjubConcrete01.' + name + '\n#print axioms ShielddSecurity.SDKJubjubConcrete01.' + name for name in names)
source.write_text(body + '\n' + audit + '\n', encoding='utf-8', newline='\n')
text = prior.read_text().replace('ConcreteSubgroupAdmission01', 'SDKJubjubConcrete01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01', 'transfer-sdk-concrete-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 402", "floor['objects'] == 403")
text = text.replace('assert len(names) == 7', 'assert len(names) == 2')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.SDKJubjubExtended01', 'ShielddSecurity.ConcreteCofactorModel01']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION', 'ACTUAL_CONCRETE_SDK_ARITHMETIC_SOURCE_MODEL')
start = text.index("plan['scope'] = ")
end = text.index("plan['source_repairs']", start)
scope = 'Concrete specialization of separately qualified SDK Extended source-model addition and doubling to the actual closed Jubjub curve model. Two full type/axiom audits. Primitive Rust field/code representation correspondence, SDK SPEND_AUTH equality, and full Transfer remain open. No runtime, BMC, control or certification credit.'
text = text[:start] + "plan['scope'] = " + repr(scope) + '\n' + text[end:]
text = text.replace('pin(Path(__file__)), pin(source)', "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-extended-model-20261010-03' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKJubjubExtended01.lean']]\nplan['source_repairs'] =")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Two-audit concrete SDK bridge recipe; unchanged physical guards.')
