"""Qualify existing handwritten native nonidentity arithmetic in complete414 context."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = Path('C:/src/shieldd-formal/circuits/ShielddSecurity/GroupNativeNonidentity.lean')
body = '\n'.join(line for line in source.read_text().splitlines() if not (
    line.strip() == 'set_option pp.all true in' or line.lstrip().startswith('#check ') or
    line.lstrip().startswith('#print axioms '))) + '\n'
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/GroupNativeNonidentity.lean').write_text(body, encoding='utf-8', newline='\n')
text = (ROOT.parent / 'transfer-sdk-encoding-injective-model-20261010-02/prepare_recipe.py').read_text()
text = text.replace('SDKEncodingInjective01', 'GroupNativeNonidentity')
text = text.replace('== 10', '== 3')
text = text.replace('transfer-sdk-codec-owned-floor-20261010-01', 'transfer-sdk-encoding-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 411", "floor['objects'] == 414")
text = text.replace("['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01']", "['ShielddSecurity.GroupByteCodec']")
start = text.index('scope = '); end = text.index('text = text[:start]', start)
scope = 'Qualify existing handwritten native nonidentity arithmetic: x-zero implies two-torsion; odd scalar-order subgroup and independent nonidentity exclude x-zero; canonical reciprocal satisfies x inverse. Three full audits. No native Rust primitive/original-row/full Transfer/runtime/control/certification credit.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Three-audit native nonidentity prerequisite source prepared.')
