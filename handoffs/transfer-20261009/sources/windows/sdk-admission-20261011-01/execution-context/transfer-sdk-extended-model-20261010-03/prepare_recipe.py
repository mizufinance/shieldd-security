"""Append audit commands and prepare a fresh source-model plan, no Lean run."""
import ast
import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py'
source = ROOT / 'handwritten/SDKJubjubExtended01.lean'
body = source.read_text()
assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:structure|theorem|lemma|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == len(set(names))
audits = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKJubjubExtended01.' + name +
                   '\n#print axioms ShielddSecurity.SDKJubjubExtended01.' + name for name in names)
source.write_text(body + '\n' + audits + '\n', encoding='utf-8', newline='\n')
text = prior.read_text()
text = text.replace('ConcreteSubgroupAdmission01', 'SDKJubjubExtended01')
text = text.replace('(?:theorem|lemma|def)', '(?:structure|theorem|lemma|def)')
text = text.replace('assert len(names) == 7', 'assert len(names) == ' + str(len(names)))
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']",
                    "'imports': ['ShielddSecurity.GroupNativeMultiply']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION', 'SDK_FIVE_COORDINATE_ARITHMETIC_SOURCE_MODEL')
start = text.index("plan['scope'] = ")
end = text.index("plan['source_repairs']", start)
scope = 'Handwritten source model of pinned jubjub0.10.0 ExtendedPoint, CompletedPoint, to_niels, extended add and double, normalization and identity test. Algebraic collapse into the accepted owned extended arithmetic retains nonzero Z and split-T integrity, accounts for opposite projective doubling sign, and proves symbolic affine addition/doubling; concrete specialization is separately scheduled. ' + str(len(names)) + ' full type/axiom audits. Rust field/byte/code representation correspondence and full Transfer remain open. No runtime testing, BMC, negative-control or certification credit.'
text = text[:start] + "plan['scope'] = " + repr(scope) + '\n' + text[end:]
text = text.replace("pin(Path(__file__)), pin(source)", "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
text = text.replace("pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)", "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'split_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-extended-model-20261010-01' / name) for name in ['events.jsonl', 'plan.json', 'review.json', 'handwritten/SDKJubjubExtended01.lean', 'runs/01-SDKJubjubExtended01/stdout.txt']]\nplan['source_repairs'] =")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-extended-model-20261010-02' / name) for name in ['events.jsonl', 'plan.json', 'review.json', 'handwritten/SDKJubjubExtended01.lean', 'runs/01-SDKJubjubExtended01/stdout.txt']]\nplan['source_repairs'] =")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print({'audits': len(names), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
