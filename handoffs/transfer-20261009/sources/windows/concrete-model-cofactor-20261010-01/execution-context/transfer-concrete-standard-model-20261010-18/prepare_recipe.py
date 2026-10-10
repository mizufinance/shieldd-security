"""Fresh plan declaration correction; no runner or physical safeguard change."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-16/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == 'a328b42cec26f0dd0d0689ece408340e5e830bab1b1edd38447f4c3695120241'
text = prior.read_text()
needle = "plan['owned_imports'] = owned\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "plan['limits']['all_bytes'] = 128 * 1024**2\n")
text = text.replace("records = [pin(Path(__file__)),", "records = [pin(Path(__file__))] + [pin(DIAG / 'transfer-concrete-standard-model-20261010-16' / name) for name in ['plan.json', 'prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'review.json', 'preflight-rejection.json']] + [")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Predecessor recipe SHA256 ' + hashlib.sha256(prior.read_bytes()).hexdigest())
