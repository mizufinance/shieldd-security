"""Prepare a symbolic mathematical SDK iterator bridge; no guard changes."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'handwritten/SDKByteIterator01.lean'
body = source.read_text(); assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == 11
audits = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKByteIterator01.'+name+'\n#print axioms ShielddSecurity.SDKByteIterator01.'+name for name in names)
source.write_text(body+'\n'+audits+'\n',encoding='utf-8',newline='\n')
text = (ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py').read_text()
text = text.replace('ConcreteSubgroupAdmission01','SDKByteIterator01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01','transfer-sdk-spend-auth-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 402", "floor['objects'] == 408")
text = text.replace('assert len(names) == 7','assert len(names) == 11')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.GroupScalarCodec']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION','SYMBOLIC_SDK_BYTE_ITERATOR_CORRESPONDENCE')
start = text.index("plan['scope'] = "); end = text.index("plan['source_repairs']",start)
scope = 'Symbolic mathematical reflection of SDK reverse-byte, reverse-inner-bit, skip-four multiplication iterator into the 252-bit reader. Generic range-block recurrence, no wide unrolled walk. Eleven full type/axiom audits. Actual Rust iterator/field/byte representation and full Transfer remain open. No runtime/BMC/control/certification credit.'
text = text[:start]+"plan['scope'] = "+repr(scope)+'\n'+text[end:]
text = text.replace('pin(Path(__file__)), pin(source)', "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Eleven-audit symbolic byte iterator recipe; physical guards unchanged.')
