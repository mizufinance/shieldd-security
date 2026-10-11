"""Make a fresh complete first package; retain every predecessor unchanged."""
from pathlib import Path
import ast
import hashlib

ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-cofactor-owned-floor-20261010-02/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '804ae2abf1ec09bcd560febd2a22ace54d205fd7b6872b0eb137c492898b6763'
text = prior.read_text()
assert text.count("('transfer-concrete-standard-model-20261010-22', 3)]") == 1
text = text.replace("('transfer-concrete-standard-model-20261010-22', 3)]",
                    "('transfer-concrete-standard-model-20261010-22', 3),\n          ('transfer-concrete-cofactor-model-20261010-02', 1)]")
assert text.count('assert len(selected) == 401') == 1
text = text.replace('assert len(selected) == 401', 'assert len(selected) == 402')
text = text.replace('plus17 newly qualified addition/model/native-contract objects.',
                    'plus18 newly qualified addition/model/native-contract/cofactor objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Fresh complete402-object floor recipe prepared; no Lean or new proof credit.')
