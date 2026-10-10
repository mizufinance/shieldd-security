"""Prepare the next five named modules after the first corrected batch passes."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-03/prepare.py'
with prior.open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest() == 'b17286f731a2defd42154806bbae4b07fe2a84d2a3d896c8063f684987ad3ddc'
text = prior.read_text()
text = text.replace("PRIOR = DIAG / 'transfer-concrete-closed-cardinality-20261010-01'",
                    "PRIOR = DIAG / 'transfer-concrete-standard-model-20261010-03'")
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['EdwardsExceptionalClassification01', 'ConcretePoleAddition01', 'EdwardsSecantPolynomials01', 'EdwardsSecantRational01', 'ConcreteSecantAddition01']" + text[end:]
start = text.index('old = ')
end = text.index('ast.parse(runner_text)', start)
text = text[:start] + "assert 'Unexpected initial owned object location' in runner_text\n" + text[end:]
text = text.replace("Fresh successor replays five maintained handwritten addition modules. EdwardsTorsionAlgebra01 removes one redundant ring after field_simp; rejected warning attempt preserved with zero credit. Full types/standard axioms; native/full Transfer open.",
                    "Replay five exceptional/secant addition modules after the corrected first batch. All retained failed receipts remain zero credit. Full types and standard axioms; native/full Transfer open.")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared second batch recipe only.')
