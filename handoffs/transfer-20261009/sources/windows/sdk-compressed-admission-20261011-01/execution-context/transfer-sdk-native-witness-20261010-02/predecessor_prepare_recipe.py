"""Qualify existing native witness arithmetic against complete415 package."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = Path('C:/src/shieldd-formal/circuits/ShielddSecurity/GroupNativeSubgroupWitness.lean')
body = '\n'.join(line for line in source.read_text().splitlines() if not (
    line.strip() == 'set_option pp.all true in' or line.lstrip().startswith('#check ') or
    line.lstrip().startswith('#print axioms '))) + '\n'
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/GroupNativeSubgroupWitness.lean').write_text(body, encoding='utf-8', newline='\n')
text = (ROOT.parent / 'transfer-sdk-encoding-injective-model-20261010-02/prepare_recipe.py').read_text()
text = text.replace('SDKEncodingInjective01', 'GroupNativeSubgroupWitness')
text = text.replace('== 10', '== 4')
text = text.replace('transfer-sdk-codec-owned-floor-20261010-01', 'transfer-sdk-native-nonidentity-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 411", "floor['objects'] == 415")
text = text.replace("['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01']", "['ShielddSecurity.GroupNativeCofactor', 'ShielddSecurity.GroupNativeNonidentity']")
start = text.index('scope = '); end = text.index('text = text[:start]', start)
scope = 'Qualify existing handwritten native subgroup witness arithmetic in full concrete-capable package. All six owned witness values are constructed from actual subgroup/nonidentity and global mathematical field/codec/model contracts. Four full audits including shared inverse and DoubleConstraints definitions. Native primitive Rust/original rows/copies/full Transfer/runtime/control/certification remain OPEN.'
text = text[:start] + 'scope = ' + repr(scope) + '\n' + text[end:]
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Four-audit native subgroup witness prerequisite prepared.')
