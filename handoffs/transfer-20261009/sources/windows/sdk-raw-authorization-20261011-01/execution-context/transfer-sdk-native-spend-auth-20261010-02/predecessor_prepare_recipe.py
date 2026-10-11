"""Exact SDK base removes generator-order premise, retaining global primitive contracts."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-owned-programs-20261010-01/prepare.py').read_text()
text = text.replace('transfer-sdk-program-owned-floor-20261010-01', 'transfer-sdk-owned-program-floor-20261010-01')
text = text.replace("floor['objects'] == 421", "floor['objects'] == 424")
text = text.replace("'owned_objects': 421", "'owned_objects': 424")
text = text.replace("    assert pin(record['prior_handwritten']['path']) == record['prior_handwritten']", "    if 'prior_handwritten' in record:\n        assert pin(record['prior_handwritten']['path']) == record['prior_handwritten']")
text = text.replace("inputs += [pin(source), pin(target), record['prior_handwritten']]", "inputs += [pin(source), pin(target)]\n    if 'prior_handwritten' in record:\n        inputs.append(record['prior_handwritten'])")
text = text.replace('OWNED_SDK_SCALAR_AND_PREIMAGE_PROGRAMS', 'CONCRETE_SDK_NATIVE_GENERATOR_AND_PROGRAM_BRIDGE')
start = text.index("plan['scope'] ="); end = text.index("\nplan['source_repairs']", start)
scope = 'Concrete SDK base identifies the globally coordinate-bound SpendAuth generator, derives its exact order/nonidentity and owned scalar-one reader result, joins production randomization to the proved mathematical SDK/native arithmetic and derives independent output-admitted witness constraints. Two owned authorization/Point prerequisites audited. Global Rust/FFI primitive contracts and original rows/copies/full Transfer remain OPEN. No runtime/BMC/control/certification credit.'
text = text[:start] + "plan['scope'] = " + repr(scope) + text[end:]
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Three-module concrete SDK/native bridge recipe prepared.')
