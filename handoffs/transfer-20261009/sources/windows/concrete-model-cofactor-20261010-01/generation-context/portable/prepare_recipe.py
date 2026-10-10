"""Fresh portability-check correction; preserve the rejected helper."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-edwards-polynomial-generation-20261010-03/prepare_portable.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == 'cde4153e3f759c8bec95fc395718b04ce0e546fcd0c00fcdabdef47dab3fc89e'
text = prior.read_text()
text = text.replace("assert 'C:/src/' not in text", "assert 'PUB = Path(' not in text and 'RECIPES = PUB' not in text")
ast.parse(text)
(ROOT / 'prepare_portable.py').write_text(text, encoding='utf-8', newline='\n')
print('Retained predecessor helper SHA256 ' + hashlib.sha256(prior.read_bytes()).hexdigest())
