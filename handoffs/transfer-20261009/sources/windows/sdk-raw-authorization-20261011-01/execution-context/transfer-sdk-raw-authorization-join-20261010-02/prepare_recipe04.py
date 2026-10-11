"""Explicit already-pinned OfFn dependency for the global array byte join."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
source = ROOT / 'prepare_stage.py'
old = source.read_text()
text = old.replace("['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw']",
                   "['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw', 'Mathlib.Data.List.OfFn']")
assert text != old and not (ROOT / 'plan.json').exists()
text = text.replace("pin(ROOT / 'prepare_recipe03.py'),", "pin(ROOT / 'prepare_recipe03.py'), pin(ROOT / 'prepare_recipe04.py'), pin(ROOT / 'predecessor_prepare_stage03.py'),")
ast.parse(text)
backup = ROOT / 'predecessor_prepare_stage03.py'
assert not backup.exists()
backup.write_bytes(source.read_bytes())
source.write_text(text, encoding='utf-8', newline='\n')
print('Explicit pinned Mathlib.Data.List.OfFn import declared; unchanged external/physical floors.')
