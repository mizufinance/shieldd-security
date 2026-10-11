"""Six exact-order/inverse audits for the independent certified SDK base."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-encoding-injective-model-20261010-02/prepare_recipe.py').read_text()
text = text.replace('SDKEncodingInjective01', 'SDKSpendAuthOrder01').replace('== 10', '== 6')
text = text.replace('transfer-sdk-codec-owned-floor-20261010-01', 'transfer-sdk-native-witness-owned-floor-20261010-02')
text = text.replace("floor['objects'] == 411", "floor['objects'] == 416")
text = text.replace("['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01']", "['ShielddSecurity.SDKCodecJoin01', 'ShielddSecurity.GroupNativeNonidentity', 'ShielddSecurity.SubgroupOrderPrime06']")
start = text.index('scope = '); end = text.index('text = text[:start]', start)
scope = 'Actual independently certified mathematical SDK SpendAuth base is nonidentity and has exact prime scalar order. Canonical positive bounded multiples are nonidentity subgroup points and have legal owned x inverses. Six full audits. No exact-order premise for the SDK base. Rust primitive/SDK source representation, native rows/copies, full Transfer/runtime/control/certification remain OPEN.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Six-audit exact SDK-base order recipe prepared.')
