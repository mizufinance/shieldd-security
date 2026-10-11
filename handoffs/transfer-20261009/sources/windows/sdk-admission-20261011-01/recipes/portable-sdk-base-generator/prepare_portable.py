"""Make the accepted certificate generator portable, retaining exact source output."""
import ast
import hashlib
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
GEN = ROOT.parent / 'transfer-sdk-spend-auth-generation-20261010-01'
prior = GEN / 'generate.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '8d08907d9661d634891ea22f7ccccb14d32c0cd0434cf0ea455d938e27f72497'
text = prior.read_text()
old = "ROOT.parent / 'transfer-sdk-spend-auth-proposal-20261010-01/proposals.json'"
assert text.count(old) == 1
text = text.replace(old, "ROOT / 'inputs/proposals.json'")
ast.parse(text)
(ROOT / 'inputs').mkdir(exist_ok=False)
shutil.copyfile(ROOT.parent / 'transfer-sdk-spend-auth-proposal-20261010-01/proposals.json', ROOT / 'inputs/proposals.json')
(ROOT / 'generate.py').write_text(text,encoding='utf-8',newline='\n')
print('Portable generator differs only by proposal path; kernel source output must match exactly.')
