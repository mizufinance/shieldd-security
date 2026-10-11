"""Prepare symbolic SDK scalar multiplication model, no Lean run."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'handwritten/SDKJubjubMultiply01.lean'
body = source.read_text()
assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == len(set(names))
audits = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKJubjubMultiply01.' + name + '\n#print axioms ShielddSecurity.SDKJubjubMultiply01.' + name for name in names)
source.write_text(body + '\n' + audits + '\n', encoding='utf-8', newline='\n')
text = (ROOT.parent / 'transfer-sdk-concrete-model-20261010-01/prepare.py').read_text()
text = text.replace('SDKJubjubConcrete01', 'SDKJubjubMultiply01')
text = text.replace('transfer-sdk-concrete-owned-floor-20261010-01', 'transfer-sdk-multiply-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 403", "floor['objects'] == 404")
text = text.replace('assert len(names) == 2', 'assert len(names) == ' + str(len(names)))
text = text.replace("'imports': ['ShielddSecurity.SDKJubjubExtended01', 'ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.SDKJubjubConcrete01', 'ShielddSecurity.GroupScalarCodec']")
text = text.replace('ACTUAL_CONCRETE_SDK_ARITHMETIC_SOURCE_MODEL', 'SYMBOLIC_CONCRETE_SDK_MULTIPLY_SOURCE_MODEL')
start = text.index("plan['scope'] = ")
end = text.index("plan['source_repairs']", start)
scope = 'Symbolic model of pinned SDK 252-bit reversed double-and-add using five-coordinate Extended/ExtendedNiels operations, identity selector, canonical little-endian integer bit reader and exact FR_MODULUS_BYTES value. Concrete group multiplication and subgroup test equivalence. Primitive Rust field/byte/iterator representation refinement and SDK SPEND_AUTH equality remain open; no runtime/BMC/control/certification credit; full Transfer open.'
text = text[:start] + "plan['scope'] = " + repr(scope) + '\n' + text[end:]
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-concrete-model-20261010-01' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKJubjubConcrete01.lean']]\nplan['source_repairs'] =")
text = text.replace("pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)", "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-multiply-model-20261010-01' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKJubjubMultiply01.lean', 'runs/01-SDKJubjubMultiply01/stdout.txt']]\nplan['source_repairs'] =")
text = text.replace("pin(ROOT / 'prepare_recipe.py'), pin(source)", "pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'repair_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-multiply-model-20261010-02' / name) for name in ['plan.json', 'events.jsonl', 'review.json', 'handwritten/SDKJubjubMultiply01.lean', 'runs/01-SDKJubjubMultiply01/stdout.txt']]\nplan['source_repairs'] =")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print({'audits': len(names), 'memory_guards': 'unchanged'})
