"""Prepare ten compressed admission/native constraint audits with unchanged guards."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-encoding-injective-model-20261010-02/prepare_recipe.py').read_text()
text = text.replace('SDKEncodingInjective01', 'SDKCompressedAdmission01')
text = text.replace('transfer-sdk-codec-owned-floor-20261010-01', 'transfer-sdk-encoding-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 411", "floor['objects'] == 414")
text = text.replace("['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01']", "['ShielddSecurity.SDKEncodingInjective01', 'ShielddSecurity.SDKCodecJoin01', 'ShielddSecurity.GroupNativeSubgroupWitness']")
start = text.index('scope = '); end = text.index('text = text[:start]', start)
scope = 'Mathematical compressed-point curve/encoding/modulus/nonidentity admission derives actual concrete subgroup and nonidentity, globally unique decoded point and all six owned native witness arithmetic constraints. SDK randomization subgroup and native authorization agreement are derived; randomized output identity gate remains explicit. Ten full type/axiom audits. Primitive native Rust field/bytes/decoder/SDK instantiation, original compiler rows/copies and full Transfer remain OPEN. No runtime/BMC/control/certification credit.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Ten-audit admission source recipe; complete414 floor mandatory.')
