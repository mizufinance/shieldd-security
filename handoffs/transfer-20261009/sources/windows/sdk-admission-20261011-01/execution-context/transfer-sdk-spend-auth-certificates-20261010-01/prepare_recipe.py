"""Prepare one generated certificate module; no Lean run."""
import ast
import hashlib
import re
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
GEN = DIAG / 'transfer-sdk-spend-auth-generation-20261010-01'
source = GEN / 'generated/SDKSpendAuthCertificates01.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == 'f3f01b7a687eb9cf166c179e938884487d48697563fd88598c05f456c1fc32ca'
target = ROOT / 'generated' / source.name
target.parent.mkdir(exist_ok=False); shutil.copyfile(source,target)
names = re.findall(r'^(?:theorem|def) ([A-Za-z0-9_]+)',source.read_text(),re.M)
assert len(names) == 28
text = (DIAG / 'transfer-concrete-admission-model-20261010-01/prepare.py').read_text()
text = text.replace('ConcreteSubgroupAdmission01','SDKSpendAuthCertificates01')
text = text.replace('transfer-concrete-admission-owned-floor-20261010-01','transfer-sdk-admission-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 402","floor['objects'] == 406")
text = text.replace('handwritten/SDKSpendAuthCertificates01.lean','generated/SDKSpendAuthCertificates01.lean')
text = text.replace('assert len(names) == 7','assert len(names) == 28')
text = text.replace("'imports': ['ShielddSecurity.ConcreteCofactorModel01']","'imports': ['ShielddSecurity.ConcreteIntegerCertificates01', 'ShielddSecurity.Group']")
text = text.replace('ACTUAL_CONCRETE_INPUT_ADMISSION_REFLECTION','GENERATED_SDK_SPEND_AUTH_INTEGER_CERTIFICATES')
start = text.index("plan['scope'] = "); end = text.index("plan['source_repairs']",start)
scope = 'One generated integer-certificate module for the mathematical point proposed from pinned SDK Sapling SpendAuth bytes: four concrete Edwards curve equations, six doubling rows, three complete additions, canonical coordinate bounds, odd-X sign and masked little-endian Y value. The global8r/subgroup join and primitive Rust byte/decoder/field correspondence are separate; this is not an equality to the distinct retained traced base. 28 full type/axiom audits; no runtime/BMC/control/certification credit; full Transfer open.'
text = text[:start] + "plan['scope'] = " + repr(scope) + '\n' + text[end:]
text = text.replace('pin(Path(__file__)), pin(source)',"pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source)")
text = text.replace("plan['source_repairs'] = 'New handwritten input-boundary proof; no generated edits or new axioms.'", "plan['pins'] += [pin(DIAG / 'transfer-sdk-spend-auth-generation-20261010-01' / name) for name in ['generate.py', 'generation-review.json', 'generated/SDKSpendAuthCertificates01.lean']]\nplan['pins'] += [pin(DIAG / 'transfer-sdk-spend-auth-proposal-20261010-01' / name) for name in ['propose.py', 'proposals.json']]\nplan['pins'].append(pin(DIAG / 'transfer-sdk-source-binding-20261010-01/sources/reddsa-0.5.2/src/constants.rs'))\nplan['source_repairs'] = 'Generated complete module from untrusted arithmetic proposals; generation has no proof credit. Never hand edit generated Lean.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('One generated28-audit SDK base certificate plan recipe; no execution or kernel credit yet.')
