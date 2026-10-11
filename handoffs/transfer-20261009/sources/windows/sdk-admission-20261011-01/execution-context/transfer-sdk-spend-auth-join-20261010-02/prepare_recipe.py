"""Prepare SDK-specific base subgroup/native-preimage mathematical join."""
import ast
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'handwritten/SDKSpendAuthSubgroup01.lean'
body = source.read_text(); assert '#check' not in body
names = re.findall(r'^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)',body,re.M)
assert len(names) == 5
audits = '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKSpendAuthSubgroup01.'+name+'\n#print axioms ShielddSecurity.SDKSpendAuthSubgroup01.'+name for name in names)
source.write_text(body+'\n'+audits+'\n',encoding='utf-8',newline='\n')
text = (ROOT.parent / 'transfer-concrete-admission-model-20261010-01/prepare.py').read_text()
text = text.replace('ConcreteSubgroupAdmission01','SDKSpendAuthSubgroup01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01','transfer-sdk-spend-auth-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 402","floor['objects'] == 408")
text = text.replace('assert len(names) == 7','assert len(names) == 5')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']","'imports': ['ShielddSecurity.SDKSpendAuthCertificates01', 'ShielddSecurity.SDKSubgroupAdmission01']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION','ACTUAL_SDK_MATHEMATICAL_BASE_SUBGROUP_AND_PREIMAGE_JOIN')
start = text.index("plan['scope'] = "); end = text.index("plan['source_repairs']",start)
scope = 'Actual concrete curve point with the certified mathematical Edwards coordinates proposed from pinned Sapling SpendAuth bytes; subgroup membership derived from the closed global exponent and three certified doublings. SDK-modeled admitted-key randomization and owned native authorization/cofactor preimage completeness use this SDK-specific mathematical base, without asserting equality to the distinct old traced base. Five full audits. Native Rust decoder/bytes/field/iterator correspondence and full Transfer remain open. No runtime/BMC/control/certification credit.'
text = text[:start]+"plan['scope'] = "+repr(scope)+'\n'+text[end:]
text = text.replace('pin(Path(__file__)), pin(source)',"pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] =", "plan['pins'] += [pin(DIAG / 'transfer-sdk-spend-auth-generation-20261010-01' / name) for name in ['generate.py', 'generation-review.json', 'generated/SDKSpendAuthCertificates01.lean']]\nplan['source_repairs'] =")
text = text.replace("pin(ROOT / 'prepare_recipe.py'), pin(source)", "pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'preparation-recovery.json'), pin(source)")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Five-audit concrete SDK base subgroup/preimage join recipe; physical guards unchanged.')
