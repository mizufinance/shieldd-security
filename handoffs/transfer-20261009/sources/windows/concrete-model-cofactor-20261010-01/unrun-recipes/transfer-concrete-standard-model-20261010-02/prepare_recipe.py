"""Make the second finite batch recipe without changing any retained predecessor."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-01/prepare.py'
with prior.open('rb') as f:
    digest = hashlib.file_digest(f, 'sha256').hexdigest()
assert digest == '10181a55d5bff6307bc14283c7bbb37464ebbab9af58cffa1c735f802f0faee5'
text = prior.read_text()
text = text.replace("PRIOR = DIAG / 'transfer-concrete-closed-cardinality-20261010-01'",
                    "PRIOR = DIAG / 'transfer-concrete-standard-model-20261010-01'")
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['EdwardsExceptionalClassification01', 'ConcretePoleAddition01', 'EdwardsSecantPolynomials01', 'EdwardsSecantRational01', 'ConcreteSecantAddition01']" + text[end:]
start = text.index('old = ')
end = text.index('ast.parse(runner_text)', start)
text = text[:start] + "assert \"Unexpected initial owned object location\" in runner_text\n" + text[end:]
text = text.replace("records.extend([pin(runner), pin(Path(__file__)),", "records.extend([pin(runner), pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'),")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared successor recipe only; no verification credit.')
