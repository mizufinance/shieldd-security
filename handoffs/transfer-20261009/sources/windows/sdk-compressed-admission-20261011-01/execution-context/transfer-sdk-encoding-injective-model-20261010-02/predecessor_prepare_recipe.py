"""Prepare ten mathematical compressed-encoding audits with unchanged guards."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-codec-join-20261010-01/prepare_recipe.py').read_text()
text = text.replace('SDKCodecJoin01', 'SDKEncodingInjective01')
text = text.replace('== 6', '== 10')
text = text.replace("['ShielddSecurity.SDKByteIterator01', 'ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKSpendAuthSubgroup01']", "['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01']")
start = text.index('scope = '); end = text.index('text = text[:start]', start)
scope = 'Mathematical compressed encoding is injective over the full concrete curve, including zero-root and torsion points. Exact canonical32-byte integer encoding and y/parity uniqueness derive decoded point identity globally. Ten full audits. Actual native Rust field/to_bytes/array/strict decoder/sqrt representation and full Transfer remain OPEN. No runtime/BMC/control/certification credit.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
ast.parse(text)
target = ROOT / 'prepare_stage.py'
assert not target.exists()
target.write_text(text, encoding='utf-8', newline='\n')
print('Ten-audit encoding recipe prepared; complete411 floor and baseline guards retained.')
