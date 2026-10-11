"""Prepare mathematical compressed-decoder uniqueness with unchanged guards."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'handwritten/SDKCodecJoin01.lean'
body = source.read_text(); assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == 6
audits = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKCodecJoin01.'+name+'\n#print axioms ShielddSecurity.SDKCodecJoin01.'+name for name in names)
source.write_text(body+'\n'+audits+'\n',encoding='utf-8',newline='\n')
text = (ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py').read_text()
text = text.replace('ConcreteSubgroupAdmission01','SDKCodecJoin01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01','transfer-sdk-codec-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 402", "floor['objects'] == 411")
text = text.replace('assert len(names) == 7','assert len(names) == 6')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.SDKByteIterator01', 'ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKSpendAuthSubgroup01']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION','MATHEMATICAL_SDK_CODEC_SUCCESSOR')
start = text.index("plan['scope'] = "); end = text.index("plan['source_repairs']",start)
scope = 'Join the exact mathematical reverse-byte/reverse-inner-bit/skip-four loop to the concrete SDK multiplication proof, literal scalar-modulus bytes test and SDK compressed-decoder subgroup membership. Six full audits. Native Rust iterator/field/bytes/decoder correspondence and full Transfer remain open. No runtime/BMC/control/certification credit.'
text = text[:start]+"plan['scope'] = "+repr(scope)+'\n'+text[end:]
text = text.replace('pin(Path(__file__)), pin(source)', "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Nine-audit mathematical compressed decoder recipe; physical guards unchanged.')
