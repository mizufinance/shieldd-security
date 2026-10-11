"""Thirteen-audit endpoint, adding a global byte-array encoding/admission join."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'prepare_stage.py'
old = source.read_text()
assert '== 8' in old and not (ROOT / 'plan.json').exists()
text = old.replace('== 8', '== 13')
text = text.replace("pin(ROOT / 'prepare_recipe02.py'), pin(source)",
                    "pin(ROOT / 'prepare_recipe02.py'), pin(ROOT / 'prepare_recipe03.py'), pin(ROOT / 'predecessor_prepare_stage.py'), pin(source)")
text = text.replace('No runtime/BMC/negative-control/certification credit.',
                    'Global byte-array encoding meaning derives SDK injectivity/coherence and identifies the admitted actual key subgroup/nonidentity without an abstract subgroup-decoder law. No runtime/BMC/negative-control/certification credit.')
ast.parse(text)
backup = ROOT / 'predecessor_prepare_stage.py'
assert not backup.exists()
backup.write_bytes(source.read_bytes())
source.write_text(text, encoding='utf-8', newline='\n')
print('Thirteen-audit raw authorization/global byte-encoding stage prepared; all unexecuted predecessors preserved.')
