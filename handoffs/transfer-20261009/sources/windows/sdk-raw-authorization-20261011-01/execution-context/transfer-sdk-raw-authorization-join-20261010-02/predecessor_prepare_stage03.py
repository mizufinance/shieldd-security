"""Prepare mathematical compressed-decoder uniqueness with unchanged guards."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'handwritten/SDKRawAuthorization01.lean'
body = source.read_text(); assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == 13
audits = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKRawAuthorization01.'+name+'\n#print axioms ShielddSecurity.SDKRawAuthorization01.'+name for name in names)
source.write_text(body+'\n'+audits+'\n',encoding='utf-8',newline='\n')
text = (ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py').read_text()
text = text.replace('ConcreteSubgroupAdmission01','SDKRawAuthorization01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01','transfer-sdk-raw-authorization-floor-20261010-01')
text = text.replace("floor['objects'] == 402", "floor['objects'] == 432")
text = text.replace('assert len(names) == 7','assert len(names) == 13')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION','MATHEMATICAL_SDK_CODEC_SUCCESSOR')
start = text.index("plan['scope'] = "); end = text.index("plan['source_repairs']",start)
scope = 'Owned raw Scalar/coordinate reader/private scalar/encoder/Point authorization programs compose with production SDK randomization in the concrete mathematical Jubjub model. Raw generator identifies independently certified actual SDK base without an exact-order premise. Successful input admission yields actual raw authorization output; independent output admission supplies all six native witness arithmetic constraints. A concrete admitted nonidentity key cancels to identity with scalar one, proving the separate output gate necessary. Global Rust/FFI primitive contracts, original circuit rows/copies and full Transfer remain OPEN. Global byte-array encoding meaning derives SDK injectivity/coherence and identifies the admitted actual key subgroup/nonidentity without an abstract subgroup-decoder law. No runtime/BMC/negative-control/certification credit.'
text = text[:start]+"plan['scope'] = "+repr(scope)+'\n'+text[end:]
text = text.replace('pin(Path(__file__)), pin(source)', "pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'prepare_recipe02.py'), pin(ROOT / 'prepare_recipe03.py'), pin(ROOT / 'predecessor_prepare_stage.py'), pin(source)")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Nine-audit mathematical compressed decoder recipe; physical guards unchanged.')
