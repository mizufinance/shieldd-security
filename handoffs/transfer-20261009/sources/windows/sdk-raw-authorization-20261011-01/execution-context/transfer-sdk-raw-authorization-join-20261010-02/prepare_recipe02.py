"""Fresh adapter from the actual bounded stage, preserving the rejected outer recipe."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-spend-auth-order-20261010-01/prepare_stage.py').read_text()
text = text.replace('SDKSpendAuthOrder01', 'SDKRawAuthorization01').replace('== 6', '== 8')
text = text.replace('transfer-sdk-native-witness-owned-floor-20261010-02', 'transfer-sdk-raw-authorization-floor-20261010-01')
text = text.replace("floor['objects'] == 416", "floor['objects'] == 432")
text = text.replace("['ShielddSecurity.SDKCodecJoin01', 'ShielddSecurity.GroupNativeNonidentity', 'ShielddSecurity.SubgroupOrderPrime06']", "['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw']")
start = text.index('\nscope = ') + 1; end = text.index('text = text[:start]', start)
scope = 'Owned raw Scalar/coordinate reader/private scalar/encoder/Point authorization programs compose with production SDK randomization in the concrete mathematical Jubjub model. Raw generator identifies independently certified actual SDK base without an exact-order premise. Successful input admission yields actual raw authorization output; independent output admission supplies all six native witness arithmetic constraints. A concrete admitted nonidentity key cancels to identity with scalar one, proving the separate output gate necessary. Global Rust/FFI primitive contracts, original circuit rows/copies and full Transfer remain OPEN. No runtime/BMC/negative-control/certification credit.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
text = text.replace("pin(ROOT / 'prepare_recipe.py'), pin(source)", "pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'prepare_recipe02.py'), pin(source)")
ast.parse(text)
assert not (ROOT / 'prepare_stage.py').exists()
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Eight-audit raw native endpoint stage prepared; earlier syntax-rejected recipe preserved.')
