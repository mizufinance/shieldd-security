"""Six generic strict mathematical decoder roundtrip audits under unchanged guards."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-encoding-injective-model-20261010-02/prepare_recipe.py').read_text()
text = text.replace('SDKEncodingInjective01', 'SDKCompressedRoundtrip01').replace('== 10', '== 6')
text = text.replace('transfer-sdk-codec-owned-floor-20261010-01', 'transfer-sdk-native-witness-owned-floor-20261010-02')
text = text.replace("floor['objects'] == 411", "floor['objects'] == 416")
text = text.replace("['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01']", "['ShielddSecurity.SDKEncodingInjective01', 'ShielddSecurity.SDKSignSelection01']")
start = text.index('scope = '); end = text.index('text = text[:start]', start)
scope = 'General mathematical strict compressed decoder roundtrip on every concrete curve point. The curve equation supplies the square-root relation; ZIP216 zero-root/sign-one exclusion is derived, and arbitrary root selection returns the encoded point globally. Includes identity, other zero roots and torsion. Six full audits. Primitive Rust canonical field/bytes/sqrt representation and full Transfer remain OPEN. No runtime/BMC/control/certification credit.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Six-audit general mathematical compressed roundtrip recipe prepared.')
