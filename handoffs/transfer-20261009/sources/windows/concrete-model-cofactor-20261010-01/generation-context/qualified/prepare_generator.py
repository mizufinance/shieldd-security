"""Fresh generator successor; retain failed preparation and keep certificates whole."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-edwards-polynomial-generation-20261010-01/generate.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '6dd004883f5d6d4ffafa460d66f097ae044e9fca581abc581441704c562edc91'
text = prior.read_text()
text = text.replace("repr(str(ROOT / ('unwritten-' + kind + '.lean')))", "repr((ROOT / ('unwritten-' + kind + '.lean')).as_posix())")
start = text.index("emit('EdwardsSecantPolynomialY01'")
end = text.index('\noutputs = ', start)
text = text[:start] + "emit('EdwardsSecantPolynomials01', ['EdwardsWeierstrassEquiv01'], list(secant.values()))\nemit('EdwardsTangentPolynomials01', ['EdwardsWeierstrassEquiv01'], list(tangent.values()))" + text[end:]
text = text.replace('assert len(outputs) == 4', 'assert len(outputs) == 2')
text = text.replace("inputs = []; bodies = {}; derivations = {}", "inputs = [pin(ROOT / 'prepare_generator.py'), pin(ROOT.parent / 'transfer-edwards-polynomial-generation-20261010-01/generate.py')]; bodies = {}; derivations = {}")
text = text.replace('then emit smaller bounded certificates.', 'then emit complete certificates with only unused bindings removed.')
text = text.replace('Secant split into two checked identities and the original three-name API.', 'Both original certificate modules retained whole with their original theorem names.')
ast.parse(text)
(ROOT / 'generate.py').write_text(text, encoding='utf-8', newline='\n')
print('Retained predecessor generator SHA256 ' + hashlib.sha256(prior.read_bytes()).hexdigest())
