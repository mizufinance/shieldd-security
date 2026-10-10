"""Fresh handwritten correction; keep the rejected predecessor immutable."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-07/prepare.py'
digest = hashlib.sha256(prior.read_bytes()).hexdigest()
assert digest == 'ff348c475510a997d727c2fba0ccbb2b56738c57119bbdbd6aecd40b56918ea9'
text = prior.read_text()
needle = "    text = original.read_text()\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "    if module == 'ConcreteOriginAdditionPilot01':\n        assert text.count('field_simp [nonzeroX] <;> ring') == 2\n        text = text.replace('field_simp [nonzeroX] <;> ring', 'field_simp [nonzeroX]; ring')\n")
text = text.replace("for task in ['transfer-concrete-standard-model-20261010-01', 'transfer-concrete-standard-model-20261010-03']:", "for task in ['transfer-concrete-standard-model-20261010-01', 'transfer-concrete-standard-model-20261010-03', 'transfer-concrete-standard-model-20261010-07']:")
text = text.replace("plan['repairs'] = 'Return", "plan['source_repairs'] = 'Origin addition: replace two unnecessary sequence-focus operators with ordinary sequencing. Conclusions, premises and proof tactics are otherwise unchanged. Predecessor warning rejection remains zero credit.'\nplan['repairs'] = 'Return")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Predecessor recipe SHA256 ' + digest)
